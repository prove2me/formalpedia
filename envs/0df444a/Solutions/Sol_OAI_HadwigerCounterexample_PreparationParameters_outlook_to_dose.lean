-- Prove2me | solution 1 for OAI.HadwigerCounterexample.PreparationParameters.outlook_to_dose
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T23:05:57.096175+00:00
-- url     : https://prove2.me/submissions/a3e20e16-d5e1-48ff-8200-024a123ddffd

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
theorem odd_smul_bit {n : ℕ} (hn : Odd n) (x : F) : n • x = x := by
  obtain ⟨m,rfl⟩ := hn
  rw [add_smul, one_smul, mul_smul, two_smul,char_two,zero_add]

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
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ComponentIndices
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Component Indices -/

noncomputable section
namespace HadwigerCounterexample

variable {g : ℕ}

theorem card_allowed (d : Tag g) : Fintype.card {l : Tag g // allowed d l} = (g-1)/2 := by
  have : NeZero g := ⟨by have := d.isLt; omega⟩
  let T := {l : Tag g // allowed d l}
  let f (i : Fin ((g-1)/2)) : Tag g := ⟨i.val+1,by have := i.isLt; omega⟩
  have hf (i) : allowed d (f i + d) := by
    have := i.isLt
    simp only [allowed,add_sub_cancel_right,f]
    omega
  let h : Fin ((g-1)/2) → T := fun i => ⟨f i + d,hf i⟩
  have hh : Function.Bijective h := by
    constructor
    · intro i j hij
      have he : f i = f j := add_right_cancel (congrArg Subtype.val hij)
      have he' := congrArg Fin.val he
      exact Fin.ext (Nat.add_right_cancel he')
    · intro l
      have hl := l.property
      unfold allowed at hl
      let i : Fin ((g-1)/2) := ⟨(l.val-d).val-1,by omega⟩
      have hi : f i = l.val-d := Fin.ext (by dsimp only [i,f]; omega)
      refine ⟨i,Subtype.ext ?_⟩
      change f i + d = _
      rw [hi,sub_add_cancel]
  simpa using (Fintype.card_congr (Equiv.ofBijective h hh)).symm

theorem card_allowed' (l : Tag g) :
    Fintype.card {d : Tag g // allowed d l} = (g-1)/2 := by
  have : NeZero g := ⟨by have := l.isLt; omega⟩
  let h : {d : Tag g // allowed d l} ≃ {x : Tag g // allowed 0 x} := {
    toFun := fun d => ⟨l-d.val, by simpa only [allowed,sub_zero] using d.property⟩
    invFun := fun x => ⟨l-x.val, by simpa only [allowed,sub_sub_cancel,sub_zero] using
      x.property⟩
    left_inv := fun d => Subtype.ext (sub_sub_cancel _ _)
    right_inv := fun x => Subtype.ext (sub_sub_cancel _ _) }
  exact (Fintype.card_congr h).trans (card_allowed _)

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
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_BooleanLabels
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Boolean Labels -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Finset
variable {b : ℕ}

variable {p : Shape} {n : ℕ}

theorem point_eval (p : Shape) (s : Label p.b) (z : Base p.g n)
    (r : SelIdx p.b p.j) (i : AIdx p.g n) : point p s z (r,i) = monoBit s r.val * baseV z i :=
  rfl

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
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_QuadraticTesters
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.flipZ_flip _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.reciprocal_actual _root_.OAI.HadwigerCounterexample.reciprocal_twice _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
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

theorem pair_outers {I J : Type} [Fintype I] [Fintype J] (x x' : Vec I) (y y' : Vec J) :
    mpair (vecMulVec x y) (vecMulVec x' y') =
      dotProduct x x' * dotProduct y y' := by
  simp only [mpair, dotProduct,vecMulVec_apply,LinearMap.coe_mk,AddHom.coe_mk,
    Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mpair_sum {I J : Type} [Fintype I] [Fintype J] (m : Mat I J)
    {α : Type*} (s : Finset α) (f : α → Mat I J) :
    mpair (∑ i ∈ s, f i) m = ∑ i ∈ s, mpair (f i) m := by
  rw [mpair_comm,map_sum]
  exact Finset.sum_congr rfl fun i _ => mpair_comm _ _

variable (p : Shape)

theorem pick_point {n} (s) (z : Base p.g n) (u : SelIdx p.b p.j)
    (d : Block p.g) (i : ℕ) :
    dotProduct (pick p n u d i) (point p s z) = selV _ s u * readBit z d i := by
  by_cases hi : i < n
  · rw [pick,dite_eq_left hi,single_one_dotProduct,readBit,dite_eq_left hi]; rfl
  · rw [pick,dite_eq_right hi,zero_dotProduct, readBit,dite_eq_right hi,mul_zero]

theorem etab_point {n} (d : Block p.g) (s s') (z z' : Base p.g n) :
    etab p n d (vecMulVec (point p s z) (point p s' z')) = test p n d z z' := by
  unfold etab testM test
  simp only [mpair_sum,pair_outers,pick_point]
  simp [selV,emptySel]

theorem sharpM_point {n} (hj : 1 ≤ p.j) (Y) (s s') (z z' : Base p.g n) :
    mpair (sharpM p n Y) (vecMulVec (point p s z) (point p s' z')) =
      ∑ a : Fin p.b, (s a + s' a) *
        evmat (Y a) (fun i => z (Block.sharp,i)) (fun i => z' (Block.sharp,i)) := by
  simp only [sharpM,mpair_sum,mpair_smul,mpair_add,pair_outers,
    sharpPick,dite_eq_left hj,pick_point,readBit,dite_eq_left (Fin.isLt _)]
  simp [selV,emptySel,evmat,dotProduct,mulVec,Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  ring

theorem selfM_pair {n} (hj : 1 ≤ p.j) (Y) {m : Moment p n} (hm : m ∈ Wspace p n) :
    mpair (selfM p n Y) m = eta p n m := by
  unfold Wspace at hm
  induction hm using Submodule.span_induction with
  | mem m h =>
    obtain ⟨s,z,rfl⟩ := h
    simp only [selfM,mpair_sum,mpair_add,mom,sharpM_point p hj,char_two,zero_mul,
      Finset.sum_const_zero, add_zero,eta,etaO,etab,LinearMap.add_apply,
      LinearMap.sum_apply]
  | zero => simp only [map_zero]
  | add _ _ _ _ h g => rw [map_add,h,g,map_add]
  | smul _ _ _ h => rw [map_smul,h,map_smul]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CoordinateBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinate Blocks -/

noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators
variable {p : Shape} {n : ℕ}

theorem pullM_def {I J V U : Type} [Fintype V] [Fintype U] (P : Mat V I)
    (Q : Mat U J) (M : Mat V U) : pullM P Q M=Pᵀ*M*Q := rfl

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

variable [DecidableEq I] [DecidableEq J] [DecidableEq R] [DecidableEq S]

/-- Uniform law of sub-batch with Gram fixed on the batch. -/
theorem framesAt_observe {C : Mat I J → Prop} (hc : ∃ x : Mat U I × Mat U J, FramesAt C x)
    (P : Mat I R) (Q : Mat J S) {G : Mat R S} (hP : Injective P.mulVec)
    (hQ : Injective Q.mulVec) (h : ∀ M, C M → Pᵀ*M*Q=G) :
    mapW (unifOn (FramesAt (U:=U) C)) (observe P Q) = unifOn (gramGood G) := by
  apply uniform_orbit _ hc
  · intro x hx
    refine ⟨?_,inj_comp_mat _ _ hx.2.1 hP,inj_comp_mat _ _ hx.2.2 hQ⟩
    change (x.1 * P)ᵀ * (x.2 * Q) = G
    rw [← h _ hx.1,transpose_mul]
    simp only [Matrix.mul_assoc]
  · intro y z hy hz
    obtain ⟨c,hc'⟩ := move_exists G y z hy hz
    refine ⟨c.perm I J,c.invar C, fun x => ?_⟩
    have hobs : observe P Q (c.perm I J x) = (c.perm R S) (observe P Q x) :=
      Prod.ext (Matrix.mul_assoc _ _ _) (Matrix.mul_assoc _ _ _)
    rw [hobs,←hc']
    exact (c.perm R S).injective.eq_iff.symm

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

theorem effective_rank {s : Plan p n} {x : Profile p n} {i} (hx : x ∈ effective s i) :
    totalRank x ≤ planRank s := by
  apply le_trans (Finset.sum_le_sum ?_) (sPin_sum s true i)
  intro j _
  exact (Submodule.finrank_mono ((box_mem ..).mp ((effective_mem.mp hx).2 j)).1)

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
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
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

theorem asBlock_inj {g : ℕ} : Injective (@asBlock g) := by
  rintro (⟨i,j⟩|⟨⟩) (⟨k,l⟩|⟨⟩) e <;> simp_all [asBlock,Block.O,Block.S]

theorem scan_is (p : Shape) {n} (l) (s : Label p.b) (f : Flavor p.g) (x : Knobs p.g n)
    (i : ProbeIdx p.g) :
    scan p l f x i=etab p n (asBlock i) (mom p s (lit f l x)) := by
  classical
  rw [mom,etab_point]
  let d := asBlock i
  unfold scan
  split
  · rename_i he
    have hg j : readBit (lit f l x) d j=zget (x d) j := by
      by_cases h : j<n <;> simp [readBit,zget,h,lit,d,he]
    unfold tested test
    simp_rw [show ∀ j, readBit (lit f l x) (asBlock i) j=zget (x (asBlock i)) j from hg]
  rename_i he
  unfold test
  have hZ j :
      readBit (lit f l x) (asBlock i) j=0 := by
    by_cases h : j<n <;> simp [readBit,lit,h,he]
  simp_rw [hZ,zero_mul,Finset.sum_const_zero]

theorem etaScan (p : Shape) {n} (l s f) (x : Knobs p.g n) :
    (scan p l f x).sumBit=eta p n (mom p s (lit f l x)) := by
  simp only [Digest.sumBit,Digest.diagO,eta,etaO,LinearMap.add_apply,LinearMap.sum_apply]
  simp_rw [scan_is p l s]
  rfl

theorem spins_law (p : Shape) (n : ℕ) : IsLaw (spins p n) := draws_law unif_law

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

theorem generic_summary (p : Shape) (hg : 3≤p.g) (l : Tag p.g) (q y : F) :
    ∃ v : Digest p.g, v.feasible l Flavor.full ∧ v.sumBit=q ∧ v.diagO=y := by
  classical
  have hi := card_allowed' l
  obtain ⟨i,hi⟩ := show ∃ i,allowed i l from by
    have ht : 0 < Fintype.card {i : Tag p.g // allowed i l} := by omega
    obtain ⟨x⟩ := Fintype.card_pos_iff.mp ht
    exact ⟨x.val,x.property⟩
  let v : Digest p.g := Sum.elim (Pi.single (i,l) y) (fun _ => q-y)
  have hf : v.diagO=y := by
    unfold Digest.diagO; rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single l]
      · simp [v]
      · intro k _ hk; simp [v,hk]
      simp
    · intro k _ hk; simp [v,hk]
    simp
  refine ⟨v,?_,?_,hf⟩
  · rintro (⟨j,t⟩|_) hj
    · have h : (j,t) ≠ (i,l) := by
        rintro hk
        obtain rfl : j=i := congrArg Prod.fst hk
        exact hj hi
      exact Pi.single_eq_of_ne h _
    exact (hj trivial).elim
  unfold Digest.sumBit
  rw [hf]; change y+(q-y)=q
  rw [add_sub_cancel]

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

theorem on_equiv (e : A≃B) (p : B→Prop) :
    mapW (unifOn (fun x => p (e x))) e = unifOn p := by
  classical
  have h : nbr (fun x => p (e x))=nbr p := Equiv.sum_comp e (fun y => ind (p y))
  funext x
  rw [mapW_equiv_val,unifOn_val,unifOn_val]; simp only [Equiv.apply_symm_apply,h]

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

private theorem pi_unifOn {I : Type} [Fintype I] [DecidableEq I]
    {A : I→Type} [∀ i,Fintype (A i)] (p : ∀ i,A i→Prop) :
    unifOn (fun x => ∀ i,p i (x i)) = prodW (fun i => unifOn (p i)) := by
  classical
  funext x
  rw [unifOn_val]
  have he : nbr (fun x : (∀ i, A i) => ∀ i,p i (x i)) = ∏ i,nbr (p i) := by
    unfold nbr; simp_rw [ind_all]
    exact prodW_tot (fun (i : I) (x : A i) => ind (p i x))
  simp only [prodW,he,unifOn_val,ind_all,Finset.prod_div_distrib]

theorem station_split (A : GeoM f) (N : ℕ) :
    mapW (rackStation A N) (rackEquiv f N)=
      prodW (fun i => unifOn (gramGood (A i))) := by
  classical
  unfold rackStation bothPart
  rw [show mapW _ _= _ from on_equiv (rackEquiv f N)
    (fun x => ∀ i,gramGood (A i) (x i))]
  exact pi_unifOn _

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

theorem injPart_failure (f : Route I G) (N : ℕ) (k : ℝ) (h : ∀ i,num (Port f i)≤k) :
    pr unif (fun x : Rack I N => ¬injPart f x)≤num G*(2*bp (k-N)) := by
  classical
  let Q := fun x : Network f N =>
    ∀ i, Injective (x i).1.mulVec ∧ Injective (x i).2.mulVec
  have he :
      pr unif (fun x : Rack I N => ¬injPart f x)=
      pr (prodW (fun i : G => unif (α:=Rack (Port f i) N))) (fun x => ¬Q x) := by
    rw [←pi_unif,← unif_equiv (rackEquiv f N),mapW_pr]
    rfl
  rw [he]
  let P i := fun x : Rack (Port f i) N => ¬ (Injective x.1.mulVec∧Injective x.2.mulVec)
  let w : Wgt (Network f N) := prodW (fun i => unif)
  have hw : IsLaw w := prodW_law (fun _ => unif_law)
  have ht i : pr unif (P i) ≤ 2*bp (k-N) := by
    let g := fun x : PlusRack (Port f i) N => ¬Injective x.mulVec
    have hi : pr unif g≤ bp (k-N) := by
      refine unif_fail.trans (bp_le ?_)
      have he := h i
      simp only [num,Fintype.card_fin] at *
      linarith only [he]
    have hQ (x : Rack (Port f i) N) :
        P i x→ (True∧g x.2)∨(g x.1∧True) := by unfold P g; tauto
    rw [pair_unif,two_mul]
    let nz := (pairW_law (α:=PlusRack (Port f i) N) unif_law (β:=PlusRack (Port f i) N) unif_law).nz
    calc pr _ _
      _ ≤ _ := pr_mono nz hQ
      _ ≤ _ := pr_or_le nz
      _ ≤ _ := by rw [pairW_pr unif unif (fun _ : PlusRack (Port f i) N => True) g,pairW_pr unif unif g (fun _ : PlusRack (Port f i) N => True),pr_true,unif_law.total,one_mul,mul_one]
                  exact add_le_add hi hi
  have hP x (h : ¬Q x) : ∃ i,P i (x i) := Classical.byContradiction (fun g =>
    h (fun i => Classical.byContradiction (fun he => g ⟨i,he⟩)))
  have hc i :
      pr w (fun x => P i (x i))=pr unif (P i) := by
    let g (j : G) (x : Rack (Port f j) N) :=
      if h:j=i then by subst i; exact P j x else True
    have he (x : Network f N) :
        P i (x i) ↔ ∀ j,g j (x j) := by
      constructor
      · intro h j
        by_cases he : j=i
        · subst j; exact (by simpa [g])
        simp [g,he]
      · intro h; simpa [g] using h i
    simp_rw [he]; unfold w; rw [prodW_pr _ g,Finset.prod_eq_single i]
    · simp [g]
    · intro j _ hj; simp [g,hj,unif_law.total]
    simp
  refine le_trans (pr_mono hw.nz hP) ((pr_exists_le hw.nz (fun i x => P i (x i))).trans ?_)
  simp_rw [hc]
  refine (Finset.sum_le_sum fun i _ => ht i).trans_eq ?_
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,num]

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

theorem joint_map {A B : I→ Type} [∀ i,Fintype (A i)] [∀ i,Fintype (B i)]
    (w : ∀ i,Wgt (A i)) (f : ∀ i,A i→ B i) :
    mapW (prodW w) (fun x i => f i (x i))=prodW (fun i => mapW (w i) (f i)) := by
  classical
  funext x
  unfold mapW
  simp_rw [funext_iff]
  exact prodW_pr _ (fun i y => f i y=x i)

theorem peer_cap (m : Mixer p n) (N : ℕ) (hN : 2*num (Full p n)<N)
    {A B : Mat (Row p n) I} (hA : Injective A.mulVec) (hB : Injective B.mulVec) :
    mapW (rawC m N) (peer p A B)=unifOn (gramGood (pullM A B (selfM p n m.mixM))) := by
  classical
  have hh : ∃ x : Oframe p n N,FramesAt (gramCond m) x :=
    framesAt_exists (gramCond_exists m)
      (by rw [← two_mul]; simpa only [num,Fintype.card_fin] using hN)
  let U : Mat (Full p n) (Row p n) := embedMat (.inl ·)
  have he : Injective U.mulVec := embedMat_inj Sum.inl_injective
  have hP (x : Mat (Fin N) (Full p n)) : x*U=primary x := by
    unfold U; rw [mul_embedMat]; rfl
  have hS (M : Mat (Full p n) (Full p n)) (hM : gramCond m M) :
      (U*A)ᵀ*M*(U*B) = pullM A B (selfM p n m.mixM) := by
    rw [pullM_def]
    have ht : Uᵀ*M*U=selfM p n m.mixM := by
      unfold U; rw [embedMat_mul,mul_embedMat]; exact hM.1
    rw [←ht,Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
  have ht : peer p A B (N:=N)=observe (U*A) (U*B) := by
    funext x
    unfold peer observe
    rw [←Matrix.mul_assoc,← Matrix.mul_assoc,hP,hP]
  rw [ht]
  exact framesAt_observe hh _ _ (inj_comp_mat _ _ he hA) (inj_comp_mat _ _ he hB) hS

variable {g : Route I G}

theorem law_peekR (m : Mixer p n) {N : ℕ} (hN : 2*num (Full p n)<N)
    {A B : NomQuery p n g}
    (ha : ∀ i,Injective (A i).mulVec) (hb : ∀ i, Injective (B i).mulVec) :
    mapW (forumLaw m N) (peekR p g A B)=rackStation (database m A B) N := by
  classical
  let v := forumLaw m N (G:=G)
  let E := rackEquiv g N
  let w := rackStation (database m A B) N
  let f (x : Forum p n N G) := fun i => peer p (A i) (B i) (x i)
  have h : mapW v f=mapW w E := by
    unfold v f w E forumLaw
    rw [joint_map (B:=fun i => Rack (Port g i) N) (w:=fun (_:G) => rawC m N)
      (f:=fun i => peer p (A i) (B i)),station_split]
    apply congrArg (prodW (ι:=G))
    funext i
    exact peer_cap m N hN (ha i) (hb i)
  change mapW v (E.symm ∘ f)=w
  rw [←mapW_nested,h]
  funext x
  rw [mapW_equiv_val,mapW_equiv_val,Equiv.symm_symm,Equiv.symm_apply_apply]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_BoundedQueryTemplates
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
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

theorem lawNu_rack (t : Tagging p I) (q : I→F) :
    mapW (lawNu p N t q) (scatter t N) = rackWave (ownMap t q) N :=
  on_equiv ..

omit [Fintype I] in
theorem ownPart_def (t : Tagging p I) (q : I→F) {N : ℕ} (x : Keys (p:=p) t N) :
    ownPart (p:=p) t q x ↔
    (∀ i, ownOne p (t i) (q i) (x i)) ∧
      ∀ (i j : I) (e : Comp p.g) (hi : inc e (t i)) (hj : inc e (t j)), i≠j →
        dotProduct (x i ⟨e,hi⟩ true) (x j ⟨e,hj⟩ false)=0 := by
  classical
  let Q := ownPort (p:=p) t
  unfold ownPart
  rw [part_scores]
  have he i j (e : Comp p.g) (hi : inc e (t i)) (hj : inc e (t j)) :
      let a : Port Q e := ⟨⟨i,⟨e,hi⟩⟩,rfl⟩
      let b : Port Q e := ⟨⟨j,⟨e,hj⟩⟩,rfl⟩
      scoreR (scatter t N x) a b=dotProduct (x i ⟨e,hi⟩ true) (x j ⟨e,hj⟩ false) := rfl
  constructor
  · intro h
    constructor
    · rintro i ⟨e,hi⟩
      let a : Port Q e := ⟨⟨i,⟨e,hi⟩⟩,rfl⟩
      exact (he i i e hi hi).symm.trans ((h e a a).trans (Matrix.diagonal_apply_eq ..))
    intro i j e hi hj heq
    let a : Port Q e := ⟨⟨i,⟨e,hi⟩⟩,rfl⟩
    let b : Port Q e := ⟨⟨j,⟨e,hj⟩⟩,rfl⟩
    have hh : a≠b := fun h => heq (congrArg (fun x:Port Q e => x.val.1) h)
    exact (he i j e hi hj).symm.trans ((h e a b).trans (Matrix.diagonal_apply_ne _ hh))
  · rintro ⟨h,h'⟩ e ⟨⟨i,v⟩,ha⟩ ⟨⟨j,w⟩,hb⟩
    rcases v with ⟨v,hv⟩; rcases w with ⟨w,hw⟩
    change v = e at ha; change w=e at hb
    subst v; subst w
    let a : Port Q e := ⟨⟨i,⟨e,hv⟩⟩,rfl⟩
    let b : Port Q e := ⟨⟨j,⟨e,hw⟩⟩,rfl⟩
    by_cases he : i=j
    · subst j
      refine (show scoreR (scatter t N x) a.val a.val=_ from h i ⟨e,hv⟩).trans ?_
      exact (Matrix.diagonal_apply_eq (fun j : Port Q e => q j.val.1) a).symm
    have hh : a≠b := fun h => he (congrArg (fun x:Port Q e => x.val.1) h)
    refine Eq.trans (h' i j e hv hw he) ?_
    exact (Matrix.diagonal_apply_ne (fun j : Port Q e => q j.val.1) hh).symm

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

omit [DecidableEq I] in
theorem layer_zero (x : Rack I N) : phasedBy 0 x=1 := by unfold phasedBy; simp [layerPhase,mpair]

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

omit [Fintype I] in
theorem ledger_zero (E : Rail I) : ledgerM E 0=0 := by
  classical ext; simp [ledgerM]

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

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_EmpiricalInformation
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
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
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_IndependentWeightCorrelation
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent Weight Correlation -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Submodule Function Finset
open scoped BigOperators
variable {I J T : Type} [Fintype I] [Fintype J] [Fintype T]
variable [DecidableEq I] [DecidableEq J] [DecidableEq T]
variable {N : ℕ}

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem lane_abs (f : I → Wgt (Rack J N)) (hf : ∀ i x,|f i x|≤1) (T : Finset I) (x) :
    |∏ i∈T,f i (led i x)|≤1 := by
  rw [Finset.abs_prod]; exact (Finset.prod_le_prod (fun i _ => abs_nonneg _)
    (fun i _ => hf i _)).trans_eq (by simp)

omit [Fintype I] [Fintype J] [DecidableEq T] in
private theorem unchanged_true (i : I) {x : Rack (I×J) N} (e : T → I×J)
    (h : i ∉ heard e) (v : PlusRack T N) : led i (x+(upliftR e v,0)) = led i x := by
  apply Prod.ext
  · ext
    simp only [led,sectionR,Prod.fst_add,Matrix.submatrix_apply,Matrix.add_apply,
      heard_fresh v h,add_zero]
  ext; simp [led,sectionR]
omit [Fintype I] [Fintype J] [DecidableEq T] in
private theorem unchanged_false (i : I) {x : Rack (I×J) N}
    (e : T → I×J) (h : i ∉ heard e) (v : PlusRack T N) :
    led i (x+(0,upliftR e v)) = led i x := by
  apply Prod.ext
  · ext; simp [led,sectionR]
  ext
  simp only [led,sectionR,Prod.snd_add,Matrix.submatrix_apply,Matrix.add_apply,
    heard_fresh v h,add_zero]

theorem speed (M : Avenue I J)
    {i j : I} (hi : i ≠ j) {x y : J} (h : M (i,x) (j,y)=1)
    (f : I→ Wgt (Rack J N)) (hf : ∀ i x,|f i x|≤1) :
    |avg unif (fun x => phasedBy M x * brightProd f x)|≤ bp (- (N:ℝ)/2) := by
  classical
  let g (q : Rack (I×J) N) := f i (led i q)
  let P := Finset.univ.erase i
  let l (q : Rack (I×J) N) := ∏ i∈P,f i (led i q)
  have he q : brightProd f q=g q*l q := (Finset.mul_prod_erase _ _ (Finset.mem_univ _)).symm
  let X := fun _ : Unit => (i,x)
  let Y := fun _ : Unit => (j,y)
  have hr : M.submatrix X Y=1 := by ext a b; cases a; cases b; rw [Matrix.one_apply_eq]; exact h
  let r := fun _ : Rack (I×J) N => (1:ℝ)
  have hh q : phasedBy M q * brightProd f q=phasedBy M q*g q*l q*r q := by
    unfold r; rw [he]; ring
  simp_rw [hh]
  have hg q w : g (q+(0,upliftR Y w))=g q := by
    unfold g
    rw [unchanged_false i Y (by simp [heard,Y,hi]) w]
  have hl (q) w : l (q+(upliftR X w,0))=l q := Finset.prod_congr rfl (fun z hz => by
    rw [unchanged_true z X (by
      have hh := (Finset.mem_erase.mp hz).1
      simp [X,heard,hh]) w])
  refine (layerLeak M g l r X Y (fun q => hf i _) (lane_abs f hf P) hg hl (fun _ _ _ => rfl)).trans_eq ?_
  rw [hr,Matrix.rank_one]
  simp only [r,abs_one, Fintype.card_unit, Nat.cast_one,mul_one,unif_law.avg_const]

theorem speed_expand (f : I→ Wgt (Rack J N)) (hf : ∀ i x,|f i x|≤1)
    (E : Rail (I×J)) (Z : Vec E) (hx : ∀ i∈E,i.1.1≠i.2.1) :
    |avg unif (fun x => ind (traced x E Z)*brightProd f x)- bp (-(E.card:ℝ))*avg unif (brightProd f)| ≤
      bp (- (N:ℝ)/2) := by
  classical
  let F (v : Vec E) :=
    vectorPhase v Z * avg unif (fun x => phasedBy (ledgerM E v) x*brightProd f x)
  have hh : avg unif (fun x => ind (traced x E Z)*brightProd f x)=avg unif F := by
    simp_rw [rail_expand,←avg_mul]
    rw [avg_avg]; apply avg_congr
    intro x _
    unfold F
    rw [← avg_mul']
    refine avg_congr (fun i _ => ?_); ring
  let L := bp (- (N:ℝ)/2)
  let B (x : Vec E) := ind (x=0)*avg unif (brightProd f)
  have he x : |F x-B x| ≤ L := by
    unfold F B
    by_cases ht : x=0
    · subst x
      simp only [ledger_zero,layer_zero,one_mul,vectorPhase,zero_dotProduct,
        wsign_zero,ind_true,sub_self,abs_zero]
      exact (bp_pos _).le
    rw [ind_zero ht,zero_mul, sub_zero, abs_mul]
    obtain ⟨y,hy⟩ : ∃ y,x y=1 := by
      by_contra! h; exact ht (funext fun i => (bit_cases _).resolve_right (h _))
    let M := ledgerM E x
    obtain ⟨⟨⟨i,j⟩,k,l⟩,hY⟩ := y
    have hA : M (i,j) (k,l)=1 := by
      simp only [M,ledgerM,Matrix.of_apply,dite_eq_left hY]
      exact hy
    rw [vectorPhase,wsign_abs,one_mul]
    exact speed M (hx _ hY) hA f hf
  rw [hh]
  have hk :
      bp (-(E.card:ℝ))*avg unif (brightProd f)=avg unif B := by
    unfold B; rw [avg_mul]
    congr 1
    symm
    change pr unif (fun x : Vec E => x=0)=_
    rw [pr_point',unif_apply,card_space,dim_vec, Fintype.card_coe,bp_neg]
  rw [hk,← avg_sub]
  exact (abs_avg_le unif_law.nz).trans (unif_law.avg_le he)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ConditionedBatchLaws
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
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

omit [Fintype G] in
private theorem road_iff (Z : GeoM g) (x : Rack (I×J) N) :
    bothPart Z x ↔ (traced x (crossroads g) (outsideZ Z) ∧
      (∀ i,bothPart (laneM Z i) (led i x))) ∧injPart g x := by
  classical
  constructor
  · intro h
    have ht := (both_test ..).mp h
    refine ⟨⟨?_,laneGram Z x h⟩,ht.2⟩
    funext i
    exact congr_fun ((match_crowd x g Z).mpr ht.1) (⟨i.val,Finset.sdiff_subset i.property⟩ :
      ↑(crowded g))
  rintro ⟨⟨ht,hH⟩,hf⟩
  refine (both_test ..).mpr ⟨(part_scores ..).mpr ?_,hf⟩
  intro i a b
  rcases a with ⟨⟨l,x'⟩,hl⟩
  rcases b with ⟨⟨t,y⟩,hr⟩
  subst i
  let j := g (l,x')
  by_cases hh : l=t
  · subst t
    let a : Port (street g l) j := ⟨x',rfl⟩
    let b : Port (street g l) j := ⟨y,hr⟩
    exact (part_scores ..).mp ((both_test ..).mp (hH l)).1 j a b
  let z : I×J := (l,x')
  let v : I×J := (t,y)
  have hv : (z,v)∈crossroads g := Finset.mem_sdiff.mpr
    ⟨Finset.mem_filter.mpr ⟨mem_univ _,hr.symm⟩,fun h => hh (mem_filter.mp h).2⟩
  exact congr_fun ht (⟨(z,v),hv⟩ : ↑(crossroads g))

private theorem cond_reset [Nonempty H] (p : H→Prop) (f : Wgt H) (h : 0<pr unif p) :
    condMean p f=pr unif p * avg (unifOn p) f := by
  rw [←on_unif]; unfold onW
  rw [avg_norm,subW_tot]
  have he : condMean p f = avg (subW unif p) f := by simp only [avg,subW,mul_assoc]; rfl
  rw [he]
  field_simp

set_option maxHeartbeats 800000 in
private theorem lane_means (Z : GeoM g) (f : I → Wgt (Rack J N)) (hf : ∀ i x,|f i x|≤1)
    (k : ℝ) (hk : ∀ i,num (Port g i)≤k) :
    |condMean (bothPart Z) (brightProd f) - bp (-( (crossroads g).card:ℝ)) *
      ∏ i,condMean (bothPart (laneM Z i)) (f i)|≤twinkle g k N := by
  classical
  let E := crossroads g
  let F i (x : Rack J N) := ind (bothPart (laneM Z i) x)*f i x
  have hF i x : |F i x|≤1 := by
    unfold F; by_cases h : bothPart (laneM Z i) x <;> simp only [h,ind_true,ind_false,one_mul,
      zero_mul]; exact hf i x; norm_num
  have hE i (h : i∈E) : i.1.1≠i.2.1 := fun he =>
    (mem_sdiff.mp h).2 (mem_filter.mpr ⟨(mem_sdiff.mp h).1,he⟩)
  have ht := speed_expand F hF E (outsideZ Z) hE
  have hP : avg unif (brightProd F)=∏ i, condMean (bothPart (laneM Z i)) (f i) :=
    (led_uniform (prodW F)).trans (prodW_avg _ _)
  let A x := ind (traced x E (outsideZ Z))*brightProd F x
  have hA x : |A x|≤1 := by
    by_cases h : traced x E (outsideZ Z)
    · unfold A; rw [ind_one h,one_mul]; exact lane_abs F hF _ x
    unfold A; rw [ind_zero h,zero_mul]; norm_num
  have hi x :
      ind (bothPart Z x) * brightProd f x= ind (injPart g x) * A x := by
    rw [road_iff]; unfold A F
    simp only [ind_and, ind_all,brightProd,Finset.prod_mul_distrib]
    ring
  have hg :
      |condMean (bothPart Z) (brightProd f) - avg unif A|≤ num G*(2*bp (k-N)) := by
    unfold condMean
    simp_rw [hi]
    rw [← avg_sub]
    refine (abs_avg_le unif_law.nz).trans ((avg_mono unif_law.nz (g:=fun x =>
      ind (¬injPart g x)) fun i => ?_).trans (injPart_failure g N k hk))
    by_cases h : injPart g i <;>
      simp only [h,ind_true,not_true,ind_false,one_mul,sub_self,abs_zero,zero_mul,zero_sub,
        abs_neg,not_false_eq_true]; exact le_rfl; exact hA _
  rw [hP] at ht
  unfold twinkle
  apply le_trans _ (add_le_add hg ht)
  exact abs_sub_le ..

omit [DecidableEq I] in
theorem lane_norm (Z : GeoM g) (hN : ∀ i, 2*num (Port g i)-(N:ℝ)≤ -1)
    (i : I) : 0<pr unif (bothPart (laneM Z i) (N:=N)) := by
  have he j : Injective (condLane g i j) := by intro a b h; exact Subtype.ext (congrArg
    (fun x : Port g j => x.val.2) h)
  have hx j : num (Port (street g i) j)≤num (Port g j) := by
    exact_mod_cast Fintype.card_le_of_injective _ (he j)
  refine lt_of_lt_of_le (inv_pos_of_pos netFact_pos) (net_norm (laneM Z i) N (fun j => ?_)).1
  linarith only [hx j,hN j]

set_option maxHeartbeats 800000 in
theorem compare_lanes (Z : GeoM g) (f : I→ Wgt (Rack J N)) (hf : ∀ i x,|f i x|≤1)
    (k : ℝ) (hk : ∀ i,num (Port g i)≤k) (hN : ∀ i,2*num (Port g i)-(N:ℝ)≤ -1) :
    |avg (rackStation Z N) (brightProd f)- ∏ i,avg (rackStation (laneM Z i) N) (f i)|≤
      2*netFact g*twinkle g k N := by
  classical
  let A := pr unif (bothPart (N:=N) Z)
  let B i := pr unif (bothPart (N:=N) (laneM Z i))
  let u := avg (rackStation Z N) (brightProd f)
  let v i := avg (rackStation (laneM Z i) N) (f i)
  let P := bp (- ((crossroads g).card:ℝ))*(∏ i, B i)
  let V := ∏ i,v i
  have hV : |V|≤1 := by
    unfold V
    rw [Finset.abs_prod]
    have he (i) :
        SubLaw (rackStation (laneM Z i) N) := unifOn_sub _
    refine (Finset.prod_le_prod (fun i _ => abs_nonneg _)
      (fun i _ => (abs_avg_le (he i).nz).trans ((he i).avg_le zero_le_one (hf i)))).trans_eq ?_
    simp
  have hh := net_norm Z N hN
  have h0 : 0<A := (inv_pos_of_pos netFact_pos).trans_le hh.1
  have h1 : |A*u-P*V|≤twinkle g k N := by
    have hb := lane_norm (N:=N) Z hN
    have ht := lane_means Z f hf k hk
    rw [cond_reset (bothPart (N:=N) Z) _ h0] at ht
    simp_rw [cond_reset _ _ (hb _)] at ht; rw [Finset.prod_mul_distrib] at ht
    simpa only [A,B,u,v,P,V,rackStation,mul_assoc] using ht
  have h2 : |A-P|≤ twinkle g k N := by
    let F (i:I) := fun _ : Rack J N => (1:ℝ)
    have ht := lane_means Z F (by intro i x; simp [F]) k hk
    have he (i : I) :
        condMean (bothPart (laneM Z i)) (F i)=B i := by simp only [F,condMean,mul_one]; rfl
    have hx :
        condMean (bothPart (N:=N) Z) (brightProd F)=A := by
      simp only [F,brightProd,condMean,Finset.prod_const_one,mul_one,A,pr]
    simp_rw [he,hx] at ht; exact ht
  have hg : A * |u-V|≤2*twinkle g k N := by
    have hh : |(A-P)*V|≤twinkle g k N := by
      rw [abs_mul]; exact ((mul_le_mul_of_nonneg_left hV (abs_nonneg _)).trans_eq (mul_one _)).trans h2
    calc A*|u-V|= |(A*u-P*V)-(A-P)*V| := by
                 rw [show A*u-P*V-(A-P)*V=(A*(u-V)) by ring,abs_mul,abs_of_nonneg h0.le]
         _ ≤ _ := ((abs_sub ..).trans (add_le_add h1 hh)).trans_eq (two_mul _).symm
  apply le_of_mul_le_mul_left _ (inv_pos_of_pos (netFact_pos (f:=g)))
  exact ((mul_le_mul_of_nonneg_right hh.1 (abs_nonneg _)).trans hg).trans_eq (by
    have h := netFact_pos (f:=g)
    field_simp)

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

theorem poUse (A B : J→NomQuery p n f) (m : Mixer p n)
    (hN : 2*num (Full p n)<N)
    (ha : ∀ i,Injective (pooled A i).mulVec) (hb : ∀ i, Injective (pooled B i).mulVec)
    (F : Wgt (Rack (J×I) N)) :
    avg (forumLaw m N) (fun x => F (peekR p (tied f J) (pooled A) (pooled B) x))=
      avg (rackStation (database m (pooled A) (pooled B)) N) F := by
  rw [← mapW_avg,law_peekR m hN ha hb]

set_option maxHeartbeats 800000 in
theorem pooled_batch (A B : J → NomQuery p n f) (m : Mixer p n)
    (hN : 2*num (Full p n)<N)
    (k : ℝ) (hk : ∀ i,num (Port (tied f J) i)≤k)
    (hL : 2*k-N≤-1)
    (ha : ∀ i, Injective (pooled A i).mulVec)
    (hb : ∀ i, Injective (pooled B i).mulVec)
    (F : J→ Wgt (Rack I N)) (hf : ∀ i x,|F i x|≤1) :
    let w := forumLaw (G:=G) m N
    |avg w (fun x => ∏ i, F i (peekR p f (A i) (B i) x)) -
      ∏ i, avg w (fun x => F i (peekR p f (A i) (B i) x))|≤
      2*netFact (tied f J)*twinkle (tied f J) k N := by
  classical
  let w := forumLaw m N (G:=G)
  let Z := database m (pooled A) (pooled B)
  have he i :
      avg w (fun x => F i (peekR p f (A i) (B i) x))=
        avg (rackStation (database m (A i) (B i)) N) (F i) := by
    unfold w; rw [←mapW_avg,law_peekR m hN (pool_injective ha i) (pool_injective hb i)]
  have hx :
      avg w (fun x => ∏ i, F i (peekR p f (A i) (B i) x)) =
        avg (rackStation Z N) (brightProd F) := by
    rw [show avg (rackStation Z N) _ =_ from (poUse A B m hN ha hb (brightProd F)).symm]
    refine avg_congr fun x _ => ?_
    simp_rw [brightProd, peek_pooled]
  dsimp only
  change |avg w _ - ∏ i, avg w _| ≤ _
  simp_rw [he]; rw [hx]
  have hi := compare_lanes Z F hf k hk (fun i => by linarith only [hk i,hL])
  simp_rw [Z,lane_pooled] at *
  exact hi

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

end Program
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_DependentPairConcentration
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

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ConcentrationScales
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
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

theorem raw_variance (v : Template p I) (M : ℕ) (hM : 1≤M) :
    ∀ᶠ n : ℕ in atTop, let N := M*n; ∀ (m : Mixer p n) (w : I→Wgt (Knobs p.g n)),
      (∀ i, IsLaw (w i)) → (∀ i,mapW (w i) (freePart p)=unif) → 2*num (Full p n)<N →
      ∀ T : Inputs p n I → Keys (p:=p) v.t N → ℝ, (∀ x y,|T x y|≤1) →
      let u:= raw m N
      let f:= fun o => avg (prodW w) (fun z => T z (fun i => callOne v i (z i) o))
      avg u (fun x => (f x-avg u f)^2) ≤ bp (-(1/4:ℝ)*n) := by
  let g := ownPort (p:=p) v.t
  filter_upwards [Program.variance_calendar p M g (num Bool*num I) 1 zero_lt_one hM]
    with n hn N m w hw hz hN T hT r f
  let s := v.singleP n
  let t (x : Inputs p n I) (y : Rack (KeySlots p v.t) N) := T x ((scatter v.t N).symm y)
  have hf : f = s.oexpect (prodW w) t := by
    unfold s f Program.oexpect t
    simp_rw [single_show,Equiv.symm_apply_apply]
  have h := hn m _ s t (prodW w) (prodW_law hw) (fun x y => hT _ _) hN
    (free_price v n w hw hz g (own_inj v))
  rw [one_mul] at h
  rw [hf]; exact h

end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_GramConditionedLaws
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gram Conditioned Laws -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Module LinearMap Submodule Function Finset
variable {I J G H : Type} [Fintype I] [Fintype J] [Fintype G] [Fintype H]
variable [DecidableEq I] [DecidableEq J] [DecidableEq G]
variable {g : Route (I×J) G} {N : ℕ}

theorem part_reset [Nonempty H] (p : H→Prop) (f : Wgt H) (h : 0<pr unif p) :
    partMean p f=pr unif p * avg (unifOn p) f := by
  rw [←on_unif]; unfold onW
  rw [avg_norm,subW_tot]
  have he : partMean p f = avg (subW unif p) f := by simp only [avg,subW,mul_assoc]; rfl
  rw [he]
  field_simp

theorem lane_collapse (A P u V e C : ℝ)
    (h0 : 0<C) (hA : C⁻¹ ≤ A) (hV : |V|≤1)
    (h1 : |A*u-P*V|≤e) (h2 : |A-P|≤e) :
    |u-V|≤2*C*e := by
  have hg : A * |u-V|≤2*e := by
    have hh : |(A-P)*V|≤e := by
      rw [abs_mul]; exact ((mul_le_mul_of_nonneg_left hV (abs_nonneg _)).trans_eq (mul_one _)).trans h2
    calc A*|u-V|= |(A*u-P*V)-(A-P)*V| := by
                 rw [show A*u-P*V-(A-P)*V=(A*(u-V)) by ring,abs_mul,abs_of_nonneg
                   (le_trans ((inv_pos_of_pos h0).le) hA)]
         _ ≤ _ := ((abs_sub ..).trans (add_le_add h1 hh)).trans_eq (two_mul _).symm
  apply le_of_mul_le_mul_left _ (inv_pos_of_pos h0)
  exact ((mul_le_mul_of_nonneg_right hA (abs_nonneg _)).trans hg).trans_eq (by field_simp)

set_option maxHeartbeats 500000 in
theorem compare_station {g : Route J G} (Z : GeoM g) (f : Wgt (Rack J N))
    (hf : ∀ x,|f x|≤1) (k : ℝ) (hk : ∀ i,num (Port g i)≤ k)
    (hN : 2*k-(N:ℝ)≤ -1) :
    |avg (rackStation Z N) f- avg (rackWave Z N) f| ≤
      2 * netFact g * (num G*(2*bp (k-N))) := by
  classical
  have hh i : 2*num (Port g i)-(N:ℝ)≤ -1 := by linarith only [hk i,hN]
  let A := pr unif (bothPart Z (N:=N))
  let B := pr unif (gramPart Z (N:=N))
  let Q := avg (rackWave Z N) f
  let W := avg (rackStation Z N) f
  let e := num G*(2*bp (k-N))
  have he (f : Wgt (Rack J N)) (hf : ∀ x,|f x|≤1) :
      |partMean (bothPart Z) f-partMean (gramPart Z) f|≤ e := by
    unfold partMean
    rw [←avg_sub]
    have hi (x : Rack J N) :
        |ind (bothPart Z x)*f x-ind (gramPart Z x)*f x| ≤ ind (¬injPart g x) := by
      rw [both_test]
      by_cases h : injPart g x
      · simp only [h,and_true,not_true,ind_false,sub_self,abs_zero,le_refl]
      by_cases h' : gramPart Z x
      · simpa [h,h',ind] using hf x
      simp [h,h',ind]
    exact (abs_avg_le unif_law.nz).trans
      ((avg_mono unif_law.nz hi).trans (injPart_failure g N k hk))
  have hx := (net_norm Z N hh).1
  have hA : 0<A := (inv_pos_of_pos netFact_pos).trans_le hx
  have hB : 0<B := (inv_pos_of_pos netFact_pos).trans_le (wave_norm Z N hh)
  have h1 := he f hf
  rw [part_reset (bothPart Z) f hA,part_reset (gramPart Z) f hB] at h1
  have h2 : |A-B|≤e := by
    have ht := he (fun i => 1) (by intro i; norm_num)
    simp only [partMean,mul_one] at ht
    exact ht
  have h := unifOn_sub (gramPart Z (N:=N))
  exact lane_collapse A B W Q e _ netFact_pos hx
    ((abs_avg_le h.nz).trans (h.avg_le zero_le_one hf)) h1 h2
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_UnaryQueryComparison
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unary Query Comparison -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Finset Filter Function LinearMap
variable {p : Shape} {n N : ℕ}

namespace Template

variable (v : Solo p)

theorem soloprice (q : F) :
    mapW (lawNu p N v.t (fun _ => q)) (soloeq v N)=lawOmega p N (v.t ()) q := by
  have hh : ownPart (p:=p) v.t (fun _=>q) = fun x => ownOne p _ q (soloeq v N x) := by
    funext x
    apply propext
    rw [ownPart_def]
    constructor
    · intro h; exact h.1 ()
    intro h; exact ⟨fun i => (by cases i; exact h),fun i j _ _ _ hi => (hi
      (Subsingleton.elim i j)).elim⟩
  unfold lawNu; rw [hh]; exact on_equiv ..

set_option maxHeartbeats 800000 in
theorem solo_data (x : Knobs p.g n) (m : Mixer p n) (q : F)
    (hj : 1≤p.j) (h : dialed p (v.t ()) (v.f ()) x=q) :
    let k := ownPort (p:=p) v.t
    let A := queryLaw v (fun _ => x) (g:=k)
    (∀ i,Injective (A i).mulVec)∧ database m A A = ownMap v.t (fun _=>q) := by
  classical
  intro k A
  have ht i : Subsingleton (Port k i) := ⟨fun p q => (own_inj v i)
    (Subsingleton.elim _ _)⟩
  let s := v.s (); let l:=v.t (); let f := v.f (); let z := lit f l x
  let u := point p s z
  have he i (j : Port k i) :
      (A i).col j=u := by
    unfold A queryLaw u s z f l; rcases j with ⟨⟨a,w⟩,h⟩; cases a; rfl
  constructor
  · intro i x y h
    have := ht i
    funext j
    let t : Row p n := (emptySel,none)
    have hf : A i t j=1 := congr_fun (he i j) t |>.trans (point_base_eval p s z none)
    have hh (x) : ((A i) *ᵥ x) t=x j := by
      change ∑ j,A i t j*x j=_
      rw [Finset.sum_eq_single j]
      · rw [hf,one_mul]
      · intro k _ h; exact (h (Subsingleton.elim _ _)).elim
      simp
    rw [←hh x,←hh y]; exact congr_fun h _
  funext i
  ext j t
  have h1 := ht i |>.elim j t; subst t
  unfold database ownMap
  rw [diagonal_apply_eq]
  let E := selfM p n m.mixM
  have heM : mpair E (mom p s z)=q := (selfM_pair p hj _ (Submodule.subset_span
    ⟨_,_,rfl⟩)).trans ((etaScan p l s f x).symm.trans h)
  change (pullM (A i) (A i) E) j j=q

  have hh : (pullM (A i) (A i) E) j j=evmat E ((A i).col j) ((A i).col j) := by
    rw [pullM_def,Matrix.mul_assoc]; rfl
  rw [hh,he,← mpair_outer]
  exact heM

set_option maxHeartbeats 800000 in
theorem solo_read (v : Solo p) (m : Mixer p n) (hN : 2*num (Full p n)<N)
    (x : Knobs p.g n) (q : F) (hj : 1 ≤ p.j)
    (h : dialed p (v.t ()) (v.f ()) x=q)
    (f : Wgt (AtomKey (p:=p) (v.t ()) N)) (hf : ∀ i,|f i|≤1)
    (k : ℝ) (hk : ∀ i,num (Port (ownPort (p:=p) v.t) i) ≤ k) (hK : 2*k-N≤ -1) :
    |avg (raw m N) (f ∘ (v.desc x))-avg (lawOmega p N (v.t ()) q) f| ≤
      2 * netFact (ownPort (p:=p) v.t) * (num (Comp p.g)*(2*bp (k-N))) := by
  classical
  let g := ownPort (p:=p) v.t
  let z := fun (_ : Unit) => x
  let A := v.queryLaw z (g:=g)
  let T := (v.singleP n).showKey (N:=N) z
  let W := scatter v.t N; let Q := soloeq v N
  let u := fun x => f (Q (W.symm x))
  have ht (i) : u (T i)=f (v.desc x i) := by
    unfold u T W
    rw [single_show,Equiv.symm_apply_apply]; rfl
  have hL : mapW (lawNu p N v.t (fun _ => q)) W=rackWave (ownMap v.t (fun _ => q)) N :=
    lawNu_rack ..
  obtain ⟨he,he'⟩ := solo_data v x m q hj h
  have hR : mapW (raw m N) T=rackStation (ownMap v.t (fun _ => q)) N := by
    rw [←he']; exact law_peekR (g:=g) m hN he he
  have h1 : avg (lawOmega p N (v.t ()) q) f = avg (rackWave (ownMap v.t (fun _=>q)) N) u := by
    rw [←hL,←soloprice,mapW_avg,mapW_avg]
    unfold u; simp_rw [Equiv.symm_apply_apply]; rfl
  have h2 : avg (raw m N) (f ∘ v.desc x)=avg (rackStation (ownMap v.t (fun _=>q)) N) u := by
    rw [←hR,mapW_avg]; simp_rw [ht]; rfl
  rw [h2,h1]; exact compare_station _ u (fun i=>hf _) k hk hK
end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_UnaryQueryFrequencies
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unary Query Frequencies -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Finset Filter Real Function
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
namespace Template

set_option maxHeartbeats 600000 in
theorem flat_recital (v : Solo p) (M : ℕ) (hM : 1 ≤ M) (hj : 1≤p.j) (ε : ℝ)
    (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, let N := M*n; ∀ (m : Mixer p n)
      (w : Wgt (Knobs p.g n)) (q : F), IsLaw w →
      carried w (fun x => dialed p (v.t ()) (v.f ()) x=q) →
      mapW w (freePart p)=unif → 2*num (Full p n)<N →
      ∀ T : Wgt (AtomKey (p:=p) (v.t ()) N), (∀ x,|T x|≤1) →
      pr (raw m N) (fun x => ε≤|minorCall v w T x - avg (lawOmega p N (v.t ()) q) T|) ≤
        bp (-(1/8:ℝ)*n) := by
  classical
  let c := ε/2; have hc : 0 < c := by positivity
  let g := ownPort (p:=p) v.t
  let k := num (KeySlots p v.t)
  let D := 2 * netFact g * (num (Comp p.g)* (2*bp k))
  filter_upwards [raw_variance v M hM,
    pay_div_nat (a:=1) D c hc (b:=0) zero_lt_one,
    pay_div_nat (a:=1/4) 1 (c^2) (by positivity) (b:=1/8) (by norm_num),
    (cast_tops M hM).eventually (eventually_ge_atTop (2*k+1))]
    with n hn hY hD hl N m w q hw he hZ hN T hT
  let μ := raw m N
  have hμ : IsLaw μ := raw_law m hN
  let u := minorCall v w T
  let b := avg (lawOmega p N (v.t ()) q) T
  have hR : 2 * netFact g * (num (Comp p.g)*(2*bp (k-N))) ≤ c := by
    have hz : 0 ≤ D := by
      unfold D; apply mul_nonneg (mul_nonneg (by norm_num) netFact_pos.le)
      exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (bp_pos _).le)
    have hq : (n:ℝ) ≤ N := by
      exact_mod_cast (show n ≤ N from (by unfold N; nlinarith))
    have hH : bp (-(N:ℝ))≤ bp (-(n:ℝ)) := bp_le (by linarith only [hq])
    refine le_trans ?_ ((mul_le_mul_of_nonneg_left hH hz).trans (by simpa using hY))
    rw [sub_eq_add_neg,bp_add]; unfold D; ring_nf; exact le_rfl
  change 2*k+1 ≤ (N:ℝ) at hl
  have hi : |avg μ u-b| ≤ c := by
    unfold u minorCall
    rw [avg_avg,← hw.avg_const b,← avg_sub]
    refine (abs_avg_le hw.nz).trans ?_
    rw [←hw.avg_const c]
    unfold avg
    apply Finset.sum_le_sum; intro i _
    by_cases h : w i=0
    · rw [h]; simp
    have hy :
        |avg μ (T ∘ v.desc i)-b|≤ c := le_trans
      (solo_read v m hN i q hj (not_not.mp fun he' => h (he i he'))
        T hT k (port_limit g) (by linarith only [hl])) hR
    exact mul_le_mul_of_nonneg_left hy (hw.nz i)
  have heV :
      avg μ (fun x => (u x-avg μ u)^2)≤ bp (-(1/4:ℝ)*n) := by
    let F (i : Inputs p n Unit) (y : Keys (p:=p) v.t N) := T (y ())
    have ht := hn m (fun i=>w) (fun i=>hw) (fun i=>hZ) hN F (fun i j=>hT _)
    have he' : u=fun o : Orient p n N =>
        avg (prodW (fun _ : Unit => w)) (fun z =>
          F z (fun i => callOne v i (z i) o)) := by
      funext i
      let f (x : Knobs p.g n) := T (v.desc x i)
      have hz : avg (mapW (draws Unit w) (fun x => x ())) f = _ :=
        mapW_avg (draws Unit w) _ f
      rw [draw_pick hw] at hz
      exact hz
    rw [he']; exact ht
  change pr μ (fun x => ε≤ |u x-b|)≤_
  have heQ x (h : ε≤|u x-b|) : c≤ |u x-avg μ u| := by
    have hh := abs_sub_le (u x) (avg μ u) b
    unfold c at *; linarith only [h,hh,hi]
  refine (pr_mono hμ.nz heQ).trans ((outlier hμ.nz _ _ hc heV).trans ?_)
  rw [div_le_iff₀ (by positivity : 0 < c^2)]
  simpa [mul_comm] using hD
end Template

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_QuadraticFourier
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quadratic Fourier -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Module LinearMap Submodule Function Finset
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem phase_trans (t : Vec I) (f : Wgt (Vec I)) :
    avg unif (fun y => f (y+t))=avg unif f := by
  let E : Vec I ≃ Vec I := ⟨(·+t),(·+t),add_polar t,add_polar t⟩
  exact avg_bij E unif f

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PolynomialZeroTests
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial Zero Tests -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Submodule Function
open scoped BigOperators
variable {A I J : Type} [Fintype A] [DecidableEq A]

theorem stocks_one (A : Type) [Fintype A] [DecidableEq A] (d : ℕ) (b : F) :
    (fun _ : Vec A=>b)∈ Stocks A d := by
  have hh : poly1 (∅:Finset A)∈ Stocks A d := subset_span ⟨_,by simp,rfl⟩
  have he : b • poly1 (∅:Finset A)=(fun _ : Vec A=>b) := by ext; simp [poly1]
  rw [←he]; exact Submodule.smul_mem _ _ hh
omit [Fintype A] [DecidableEq A] in
theorem stock_var (i : A) : (fun x : Vec A => x i)∈Stocks A 1 :=
  subset_span ⟨{i},by simp,by funext; simp [poly1]⟩

omit [Fintype A] in
theorem poly1_union (x : Vec A) (s t : Finset A) :
    poly1 (s∪t) x=poly1 s x*poly1 t x := by
  have he (x : Vec A) (s : Finset A) (i : A) :
      poly1 (insert i s) x=x i*poly1 s x := by
    by_cases h : i∈s
    · rw [insert_eq_of_mem h]
      unfold poly1; rw [← Finset.mul_prod_erase _ _ h,←mul_assoc,bit_sq]
    simp [poly1,h]
  induction s using Finset.induction_on with
  | empty => simp [poly1]
  | insert i s hi ih => rw [insert_union,he,he,ih,mul_assoc]

omit [Fintype A] in
set_option maxHeartbeats 600000 in
theorem stock_prod {f g : Vec (Vec A)} {d j : ℕ} (hf : f∈ Stocks A d) (hg : g∈Stocks A j) :
    f*g∈Stocks A (d+j) := by
  classical
  unfold Stocks at hf
  induction hf using Submodule.span_induction with
  | zero => simp
  | add f j _ _ hf hj => rw [add_mul]; exact Submodule.add_mem _ hf hj
  | smul p j _ hj =>
    rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hj
  | mem x hx =>
    obtain ⟨s,hs,rfl⟩ := hx
    unfold Stocks at hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t,ht,rfl⟩ := hx
      exact subset_span ⟨s∪t,(Finset.card_union_le ..).trans (add_le_add hs ht),
        funext fun x=>(poly1_union x s t).symm⟩
    | zero => simp
    | add f j _ _ hf hj => rw [mul_add]; exact Submodule.add_mem _ hf hj
    | smul p j _ hj => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hj

set_option maxHeartbeats 600000 in
theorem stock_decay (p : Vec A) {d : ℕ} {f} (h : f∈ Stocks A (d+1)) :
    spoil p f ∈ Stocks A d := by
  classical
  unfold Stocks at h
  induction h using Submodule.span_induction with
  | zero => simp
  | add f j _ _ hf hj => rw [map_add]; exact Submodule.add_mem _ hf hj
  | smul p j _ hj => rw [map_smul]; exact Submodule.smul_mem _ _ hj
  | mem x hx =>
    obtain ⟨s,hs,rfl⟩ := hx
    induction s using Finset.induction_on generalizing d with
    | empty =>
      have hi : spoil p (poly1 ∅)=0 := by funext; simp [spoil,poly1]
      rw [hi]; exact Submodule.zero_mem _
    | insert i s hi ih =>
      rw [card_insert_of_notMem hi] at hs
      have he : poly1 s∈ Stocks A d := subset_span ⟨_,by omega,rfl⟩
      let u := poly1 s
      let v := fun x : Vec A => x i+p i
      have hh :
          spoil p (poly1 (insert i s))=p i • u + v*spoil p u := by
        funext x; simp only [v,u,spoil,LinearMap.coe_mk,AddHom.coe_mk,
          poly1,Finset.prod_insert hi,Pi.smul_apply,Pi.add_apply,smul_eq_mul,Pi.mul_apply] <;> ring
      rw [hh]
      refine Submodule.add_mem _ (Submodule.smul_mem _ _ he) ?_
      cases d
      next =>
        obtain rfl : s=∅ := Finset.card_eq_zero.mp (by omega)
        have hi : spoil p u=0 := by funext; simp [spoil,u,poly1]
        rw [hi]; simp
      next d =>
        have hS : spoil p u∈ Stocks A d := ih (by omega)
        have hf : v∈ Stocks A 1 := Submodule.add_mem (Stocks A 1)
          (stock_var i) (stocks_one A 1 (p i))
        have hm := stock_prod hf hS
        rwa [Nat.add_comm 1] at hm

omit [Fintype A] [DecidableEq A] in
theorem stock_initial {f} (x y : Vec A) (h : f∈ Stocks A 0) : f x=f y := by
  unfold Stocks at h
  induction h using Submodule.span_induction with
  | zero => rfl
  | add f j _ _ hf hj => simp only [Pi.add_apply,hf,hj]
  | smul p j _ hj => simp only [Pi.smul_apply,hj]
  | mem x hx =>
    obtain ⟨s,hs,rfl⟩ := hx
    obtain rfl : s=∅ := Finset.card_eq_zero.mp (by omega)
    simp [poly1]

theorem stocks_bound (A : Type) [Fintype A] [DecidableEq A] (d : ℕ) (f : Vec (Vec A))
    (h : f∈ Stocks A d) (he : ∃ x, f x≠0) :
    bp (-(d:ℝ))≤ pr unif (fun x => f x≠0) := by
  classical
  induction d generalizing f with
  | zero =>
    obtain ⟨x,hx⟩ := he
    have he (y:Vec A) : f y≠0 := (stock_initial y x h).trans_ne hx
    simp only [pr,ind_one (he _), Nat.cast_zero, neg_zero,bp_zero,unif_law.avg_const,le_refl]
  | succ d ih =>
    by_cases hh : ∃ y, f y=0
    · obtain ⟨x,hx⟩ := he; obtain ⟨y,hy⟩ := hh
      let p := x-y
      have hZ : bp (-(d:ℝ))≤ pr unif (fun x=>spoil p f x≠0) := ih _ (stock_decay p h)
        ⟨y,by change f (y+p)-f y≠0; unfold p; rw [add_sub_cancel,hy,sub_zero]; exact hx⟩
      let P x := f x≠0
      have hg :
          pr unif (fun x=>spoil p f x≠0)≤2*pr unif P := by
        have he x (h : spoil p f x≠0) :
            P (x+p)∨P x := by
          by_contra! hh; unfold spoil at h; apply h
          unfold P at hh; simp [not_ne_iff.mp hh.1,not_ne_iff.mp hh.2]
        apply ((pr_mono unif_law.nz he).trans (pr_or_le unif_law.nz)).trans_eq
        rw [show pr unif (fun x=>P (x+p))=pr unif P from phase_trans p (fun x=>ind (P x)),two_mul]
      have hx' := hZ.trans hg
      push_cast
      rw [neg_add,bp_add,bp_neg 1,bp_one]
      linarith only [hx']
    have hz (x:Vec A) : f x≠0 := fun he=>hh ⟨x,he⟩
    simp only [pr,ind_one (hz _),unif_law.avg_const]
    rw [←bp_zero]; exact bp_le (by apply neg_nonpos.mpr; positivity)
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PointAtomVanishing
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Point Atom Vanishing -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Submodule Function Finset LinearMap
open scoped BigOperators
variable {p : Shape} {n : ℕ} {I A : Type} [Fintype I] [Fintype A]
variable [DecidableEq I] [DecidableEq A]

omit [Fintype A] in
private theorem pointPoly (f : Mat I I→ₗ[F] F) (x : Vec A→Vec I) (d : ℕ)
    (hx : ∀ i,(fun s=>x s i)∈Stocks A d) :
    (fun s=>f (vecMulVec (x s) (x s))) ∈ Stocks A (2*d) := by
  classical
  let E (i : I×I) := vecMulVec (Pi.single i.1 (1:F)) (Pi.single i.2 (1:F))
  have he (v : Vec I) :
      vecMulVec v v=∑ i:I × I,(v i.1*v i.2) • E i := by
    ext i j; rw [Matrix.sum_apply, Finset.sum_eq_single (i,j)]
    · simp [E,Matrix.vecMulVec_apply]
    · intro z _ hz
      have h : i≠z.1 ∨ j≠z.2 := not_and_or.mp (fun h=>hz (Prod.ext h.1.symm h.2.symm))
      rcases h with h|h <;> simp [E,Matrix.vecMulVec_apply,Pi.single_eq_of_ne h]
    simp
  let P (i : I × I) : Vec (Vec A) := f (E i) •
    ((fun s => x s i.1) * (fun s => x s i.2))
  have hm :
      (fun s=>f (vecMulVec (x s) (x s)))=∑ i:I×I,P i := by
    funext s; simp only [he,map_sum,map_smul,Finset.sum_apply,P,
      Pi.smul_apply, Pi.mul_apply,smul_eq_mul]; simp only [mul_comm]
  rw [hm]
  apply Submodule.sum_mem
  intro i _
  unfold P
  rw [two_mul]; exact Submodule.smul_mem _ _ (stock_prod (hx _) (hx _))

set_option maxHeartbeats 600000 in
theorem vat_erase (l : Tag p.g) (s : Label p.b) (f : Moment p n→ₗ[F] F)
    (h : pr (spins p n)
      (fun x => f (mom p s (lit Flavor.full l x)) ≠ 0)<1/4) :
    ∀ z : Base p.g n,allows l z → f (mom p s z)=0 := by
  classical
  let e : Base p.g n ≃ Knobs p.g n := ⟨curry,uncurry,fun _=>rfl,fun _=>rfl⟩
  let Z (x : Base p.g n) := lit Flavor.full l (e x)
  let Q (x : Base p.g n) := point p s (Z x)
  have he (i : Row p n) : (fun x=> Q x i)∈Stocks (BaseIdx p.g n) 1 := by
    rcases i with ⟨a,_|k⟩
    · exact stocks_one _ 1 _
    let h := monoBit s a.val
    by_cases ha : Flavor.full.keeps l k.1
    · unfold Q Z
      simp_rw [point_eval, baseV,Option.elim',lit,ite_eq_left ha]
      exact Submodule.smul_mem _ h (stock_var k)
    unfold Q Z
    simp_rw [point_eval,baseV,Option.elim',lit,ite_eq_right ha]
    exact stocks_one _ _ _
  intro z hz; by_contra ht
  have hZ : Z z=z := by
    funext i
    by_cases hh : Flavor.full.keeps l i.1
    · exact ite_eq_left hh
    rcases i with ⟨⟨d,t⟩|i,j⟩
    · exact (ite_eq_right hh).trans (hz d t hh j).symm
    exact (hh trivial).elim
  have hg := stocks_bound (BaseIdx p.g n) _ _
    (pointPoly f Q 1 he) ⟨z,(by unfold Q; rw [hZ]; exact ht)⟩
  have hpr :
      pr (spins p n) (fun x => f (mom p s (lit Flavor.full l x))≠0) =
      pr unif (fun x => f (vecMulVec (Q x) (Q x))≠0) := by
    unfold spins; rw [←draws_unif,←unif_equiv e,mapW_pr]; rfl
  rw [hpr] at h
  have hi := lt_of_le_of_lt hg h
  norm_num [bp] at hi

set_option maxHeartbeats 800000 in
theorem vat_excluded (z : Base p.g n) (E : Finset (Label p.b)) (f : Moment p n→ₗ[F] F)
    (h : ∀ s,s∉E → f (mom p s z)=0)
    (hE : (E.card:ℝ) < bp ((p.b:ℝ)-2*p.j)) : ∀ s,f (mom p s z)=0 := by
  classical
  let Q := fun s=>point p s z
  have he (i : Row p n) : (fun s=>Q s i)∈ Stocks (Fin p.b) p.j := by
    rcases i with ⟨a,b⟩
    have h : (fun s=>Q s (a,b)) = baseV z b • poly1 a.val := by
      unfold Q poly1; funext s; exact mul_comm _ _
    rw [h]; exact Submodule.smul_mem _ _ (subset_span ⟨_,a.property,rfl⟩)
  intro s; by_contra! hh
  let p' y := f (mom p y z)≠0
  have hz := stocks_bound (Fin p.b) _ _ (pointPoly f Q p.j he) ⟨s,hh⟩
  have ha := hz.trans (pr_mono unif_law.nz (p:=p') (q:=fun s=>s∈ E) fun i hi =>
    not_not.mp (fun hg=> hi (h i hg)))
  rw [pr_unif,nbr_eq_card, card_space (Vec (Fin p.b)), dim_vec,Fintype.card_fin] at ha
  have hh : Fintype.card {i // i∈E}=E.card := Fintype.card_coe E
  rw [hh,le_div_iff₀ (bp_pos _),←bp_add] at ha
  push_cast at ha
  rw [show -(2*(p.j:ℝ)) + p.b=p.b-2*(p.j:ℝ) by ring] at ha
  exact hE.not_ge ha
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CommonPredictions
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Common Predictions -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Function Finset Submodule
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

theorem atom_silent {w : Pdual p n}
    (h : ∀ l s z,allows l z → w (atom p l s z)=0) : silent w := by
  classical
  intro x hx
  obtain ⟨u,hu,rfl⟩ := mem_X.mp hx
  have he l : Wtag p n l≤LinearMap.ker (w∘ₗfixStar p n l) := by
    refine Submodule.span_le.mpr ?_
    rintro x ⟨s,z,hz,rfl⟩
    exact h l s z hz
  have ht : (cut p n u)=∑ i : Tag p.g,fixStar p n i (u i) := by
    have hh := Finset.univ_sum_single u
    unfold fixStar
    simp_rw [LinearMap.comp_apply, ← map_sum (cut p n)]
    exact congrArg (cut p n) (Eq.symm hh)
  rw [ht,map_sum]; exact Finset.sum_eq_zero fun i _=>he _ (hu i)

theorem shared_base (p : Shape) (hn : 2*p.r≤n) (hr : 1 ≤ p.r) (hg : 0 < p.g) :
    ∃ (z : Base p.g n) (s : Label p.b), (∀ l, allows l z) ∧ eta p n (mom p s z)=1 := by
  classical
  let l : Tag p.g := ⟨0,hg⟩
  let f : Flavor p.g:= Flavor.sharedOnly
  let i := (Sum.inr () : ProbeIdx p.g)
  let v : Digest p.g := Pi.single i 1
  have hx : v.feasible l f := by
    rintro (x|⟨⟩) _
    · exact Pi.single_eq_of_ne (by simp [i]) _
    exact (‹¬_› trivial).elim
  have he := exists_of_pr_pos (spins_law p n).nz
    ((scanPrice_pos p).trans_le (scan_fraction (n:=n) l f v hr hn hx))
  obtain ⟨x,h,_⟩ := he
  refine ⟨lit f l x,0,fun i d t h k => ite_eq_right (by simp [f,Flavor.keeps]),?_⟩
  rw [←etaScan,h]; simp [v,Digest.sumBit,Digest.diagO,i]

theorem atom_union (p : Shape) (n : ℕ) (z : Base p.g n) (s : Label p.b) :
    ∑ i:Tag p.g,atom p i s z=0 := by
  simp_rw [atom,←map_sum (cut p n)]
  rw [Finset.univ_sum_single (fun i : Tag p.g => mom p s z)]
  funext x
  exact char_two (mom p s z)

set_option maxHeartbeats 800000 in
theorem exact_vat (w : Pdual p n) (E : Finset (Label p.b)) (g : F)
    (hE : (E.card:ℝ)<bp ((p.b:ℝ)-2*p.j))
    (hj : Odd p.g) (hn : 2*p.r≤n) (hr : 1≤p.r)
    (h : ∀ l s,s∉E → pr (spins p n)
      (fun x => w (useAtom p l s Flavor.full x)≠g *dialed p l Flavor.full x)<1/4) :
    g=0∧ silent w := by
  classical
  let Q l := w ∘ₗ fixStar p n l - g • eta p n
  have hi (l : Tag p.g) (s : Label p.b) (z : Base p.g n) :
      Q l (mom p s z)= w (atom p l s z)-g*eta p n (mom p s z) := rfl
  have hh (l s z) (hz : allows l z) : Q l (mom p s z)=0 := by
    have he (s) (hs : s∉E) :
        pr (spins p n) (fun x=> Q l (mom p s (lit Flavor.full l x))≠0)<1/4 := by
      simp_rw [hi,←etaScan p l s Flavor.full]
      simpa only [sub_ne_zero,useAtom,dialed] using h l s hs
    exact vat_excluded z E (Q l) (fun i h=>vat_erase l i (Q l) (he i h) z hz) hE s
  simp_rw [hi] at hh
  have he l s z (h : allows l z) : w (atom p l s z) =g*eta p n (mom p s z) :=
    sub_eq_zero.mp (hh l s z h)
  obtain ⟨z,s,hz,hb⟩ := shared_base p hn hr (by obtain ⟨_,hh⟩ := hj; omega)
  have h0 : g=0 := by
    have ht : w (∑ l:Tag p.g,atom p l s z)=0 := by rw [atom_union,map_zero]
    rw [map_sum] at ht
    simp_rw [he _ s z (hz _),hb,mul_one] at ht
    simpa only [Finset.sum_const, Finset.card_univ,Tag,Fintype.card_fin,
      odd_smul_bit hj] using ht
  refine ⟨h0,atom_silent (fun i s z h=> (he i s z h).trans ?_)⟩
  rw [h0,zero_mul]
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

theorem bp_nat_vanish {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => bp (-c*n)) atTop (𝓝 0) :=
  (bp_tendsto_zero hc).comp tendsto_natCast_atTop_atTop

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

variable {s : LeafMixture p n N} {w μ : Wgt (X p n N)}
variable {D E ζ η : ℝ} {K L : ℕ}

theorem root_bound (hh : strength s w μ D ζ K) (x : X p n N) : planRank (s.rooting x) ≤ K := by
  classical
  by_cases hs : inTiles s.T x
  · rw [rooting,poller,dite_eq_left hs]
    exact (hh.leaf _ hs.choose_spec.1).bound
  unfold rooting poller; rw [dite_eq_right hs]
  exact le_of_eq_of_le (Finset.sum_eq_zero (fun i _=>finrank_bot ..)) K.zero_le

theorem sapLaw (h : 0 < s.amount w) (hw : IsLaw w) : IsLaw (s.sap w) := on_law hw.nz h

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
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PredictionExactification
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prediction Exactification -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix LinearMap Function Filter Real
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

theorem tabCalendar (p : Shape) (M : ℕ) (hM : 1≤M) (hg : 3≤ p.g) (hr : 1≤p.r) (hj : 1≤p.j)
    (l : Tag p.g) (s : Label p.b) :
    ∀ᶠ n : ℕ in atTop, let N:=M*n; ∀ (m : Mixer p n), 2*num (Full p n)<N →
    ∀ (g : Augur p N) (x f : F),
      tabRef p l x g f ≤1/100 →
      pr (raw m N) (fun i => 1/32<tabErr p l s i x g f)≤ bp (-(1/8:ℝ)*n) := by
  classical
  let v := Template.solo p l s Flavor.full
  filter_upwards [Template.flat_recital v M hM hj (1/100) (by norm_num),eventually_ge_atTop (2*p.r)]
    with n hn hq N m hN g x f he
  let w := scopedBit p n l Flavor.full x
  obtain ⟨d,hd,hg,_⟩ := generic_summary p hg l x 0
  have hw := dial_law p n l Flavor.full x hr hq ⟨d,hd,hg⟩
  have hy := normW_carried (subW_carried (spins p n) (fun i=>dialed p l Flavor.full i=x))
  let T (i : AtomKey (p:=p) l N) := ind (g l x i≠ f*x)
  have ht (i) : |T i|≤1 := by unfold T; rw [abs_of_nonneg (ind_nonneg _)]; exact ind_le_one _
  have hh := hn m w x hw hy (scopedZ_bit p n _ _ _ hw) hN T ht
  refine (pr_mono (raw_law m hN).nz (fun i hi => ?_)).trans hh
  change 1/100≤ |tabErr p l s i x g f-tabRef p l x g f|
  exact le_trans (by linarith only [he,hi]) (le_abs_self _)

theorem hushCalendar (p : Shape) (M : ℕ) (hM : 1≤M) (hg : 3≤p.g)
    (hr : 1≤p.r) (hj : 1≤p.j) :
    ∀ᶠ n : ℕ in atTop, let N:=M*n; ∀ (m : Mixer p n),2*num (Full p n)<N →
    ∀ (g : Augur p N) (x : F), (∀ i b,tabRef p i b g x≤1/100) →
    pr (raw m N) (fun i=>¬ whisper p g x i)≤bp (-(1/16:ℝ)*n) := by
  classical
  let A:= Tag p.g × Label p.b × F
  filter_upwards [eventually_all.mpr (fun i:A => tabCalendar p M hM hg hr hj i.1 i.2.1),
    pay_nat (a:=1/8) (b:=1/16) (num A) (by norm_num)]
    with n hn hd N m hN g f hw
  let T (i:A) (o:Orient p n N) := 1/32<tabErr p i.1 i.2.1 o i.2.2 g f
  have he o (h : ¬whisper p g f o) : ∃ i,T i o := by
    unfold whisper at h
    push Not at h
    obtain ⟨l,s,b,h⟩:=h; exact ⟨(l,s,b),h⟩
  have hm := raw_law m hN
  have ht (i:A) : pr (raw m N) (T i)≤bp (-(1/8:ℝ)*n) := hn i m hN g _ f (hw _ _)
  exact ((pr_mono hm.nz he).trans (pr_exists_le hm.nz T)).trans
    (((Finset.sum_le_sum (fun i _=>ht i)).trans_eq (by simp [num])).trans hd)

set_option maxHeartbeats 800000 in
theorem hush_vat (w : Pdual p n) (E : Finset (Label p.b)) (i : Orient p n N) (g : Augur p N) (f : F)
    (hE : (E.card:ℝ)< bp ((p.b:ℝ)-2*p.j)) (h : postulates p i g w E (1/16))
    (hz : whisper p g f i) (hg : Odd p.g) (hr : 1≤p.r) (hn : 2*p.r≤n) :
    f=0∧silent w := by
  classical
  refine exact_vat w E f hE hg hn hr (fun l s hs=>?_)
  let v := Template.solo p l s Flavor.full; let μ:= spins p n
  let q (x: Knobs p.g n) := dialed p l Flavor.full x
  let Q (b:F) (x) := q x=b
  let S (b:F) x := g l b (v.desc x i) ≠ f*b
  let P x:= S (q x) x
  have hμ:= spins_law p n
  have hp :
      pr μ P ≤ 2*(1/32) := by
    have ht b : pr μ (fun x=>Q b x∧S b x) ≤ 1/32 := by
      rw [pr_of_on hμ.nz]
      have hh : pr (onW μ (Q b)) (S b) ≤1/32 := hz _ _ _
      exact (mul_le_mul ((pr_le_tot hμ.nz).trans hμ.total.le) hh
        (pr_nonneg (normW_subLaw (subW_nonneg hμ.nz _)).nz) zero_le_one).trans_eq (one_mul _)
    calc _
      _ ≤ ∑ b:F,pr μ (fun i=>Q b i ∧ S b i) :=
            (pr_mono hμ.nz (fun i h=>show ∃ b,Q b i∧S b i from ⟨q i,rfl,h⟩)).trans
            (pr_exists_le hμ.nz _)
      _ ≤ _ := (Finset.sum_le_sum fun i _=>ht i).trans_eq (by simp [F,ZMod.card])
  let T x:= mismatch p g w l s Flavor.full i x
  have ht : pr μ T≤ 1/16 := h _ hs _ _
  have he x (h : w (useAtom p l s Flavor.full x)≠ f*q x) : T x∨P x := by
    by_contra! hh
    exact h ((not_ne_iff.mp hh.1).trans (not_ne_iff.mp hh.2))
  exact lt_of_le_of_lt ((pr_mono hμ.nz he).trans (pr_or_le hμ.nz)) (by linarith only [ht,hp])
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PredictionClasses
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prediction Classes -/

noncomputable section
namespace HadwigerCounterexample
open Filter Matrix Finset
open scoped BigOperators Topology

variable {p : Shape}
namespace PredictionClass

variable {U : Ultrafilter ℕ} {M : ℕ}
  {g : Bool → season p M} {α : Party}

private theorem census_active (i : Bool) :
    active (census U g α) i ↔ ¬modest U g α i := by
  classical
  unfold census
  cases i <;> split_ifs <;> simp_all [active]

private theorem census_lit :
    (census U g α).lit α := by
  classical
  constructor
  · intro i hi; exact (show modest U g α i from not_not.mp (fun h=> hi ((census_active i).mpr h))).1
  unfold census
  intro h; split_ifs at h; try contradiction
  exact ‹accords U g α›.1

theorem disappearing_add {x y : season p M} {r s : F}
    (h : disappearing U x r) (hh : disappearing U y s) :
    disappearing U (fun i => fun l q j=> x i l q j+y i l q j) (r+s) := by
  intro l q ε he
  filter_upwards [h l q _ (half_pos he),hh l q _ (half_pos he)] with i hi hj
  let v := lawOmega p (M*i) l q
  have hv (j : AtomKey (p:=p) l (M*i)) : 0≤ v j := by
    exact (unifOn_sub _).nz _
  let P j := x i l q j≠r*q
  let Q j := y i l q j≠s*q
  have hh (j) (h : x i l q j+y i l q j≠ (r+s)*q) : P j∨ Q j := by
    unfold P Q
    rw [add_mul] at h; contrapose h
    push Not at *
    simp [h]
  have hf : pr v P ≤ ε/2 := hi; have hg : pr v Q ≤ ε/2 := hj
  exact ((pr_mono hv hh).trans (pr_or_le hv)).trans (by linarith only [hf,hg])

private theorem census_match (h : accords U g α) :
    modest U g α true ↔ modest U g α false := by
  classical
  let x : season p M := fun n l q i=>g true n l q i+g false n l q i
  obtain ⟨hd,s,hs⟩:=h
  have hs : disappearing U x s := hs
  refine ⟨fun ⟨h,r,hg⟩=>⟨by simpa only [firstBit,←hd] using h,r+s,?_⟩,
    fun ⟨h,r,hg⟩=>⟨by simpa only [firstBit,hd] using h,r+s,?_⟩⟩
  · have he : (fun n l q j=>g true n l q j+x n l q j)=g false := by
      funext n l q j; change _+(_+_)=_; rw [←add_assoc,char_two,zero_add]
    rw [←he]; exact disappearing_add hg hs
  have he : (fun n l q j=>g false n l q j+x n l q j)=g true := by
    funext n l q j; change _+(_+_)=_; rw [add_left_comm,char_two,add_zero]
  rw [←he]; exact disappearing_add hg hs

set_option maxHeartbeats 1000000 in
private theorem census_echoes (i j : Bool) (s t r : F) (h : s*firstBit α i=t*firstBit α j)
    (hg : disappearing U (fun n=>assembly (fun i=>g i n) i j s t) r) :
    (census U g α).echoes i j s t := by
  classical
  unfold echoes; simp_rw [census_active]
  rcases bit_cases s with hs|hs <;> rcases bit_cases t with ht|ht <;> subst s t
  · simp
  · have hi : firstBit α j=0 := by simpa only [zero_mul,one_mul] using h.symm
    have hh : (fun n : ℕ=> assembly (fun i=>g i n) i j 0 1)=g j := by
      funext n l q x; change (0:F)*g i n l q x+ (1:F)*g j n l q x=g j n l q x; rw [one_mul,zero_mul,zero_add]
    have he : modest U g α j := ⟨hi,r,hh ▸ hg⟩
    simp [he]
  · have hi : firstBit α i=0 := by simpa only [zero_mul,one_mul] using h
    have hh : (fun n : ℕ=> assembly (fun i=>g i n) i j 1 0)=g i := by
      funext n l q x; change (1:F)*g i n l q x+ (0:F)*g j n l q x=g i n l q x; rw [one_mul,zero_mul,add_zero]
    have he : modest U g α i := ⟨hi,r,hh ▸ hg⟩
    simp [he]
  simp only [true_and]
  by_cases hv : i=j
  · subst j; simp
  have ht : accords U g α := by
    have hh : 1+α i=1+α j := by simpa only [one_mul,firstBit] using h
    have h : α i=α j := add_left_cancel hh
    let x1 (i j: Bool) := fun n=>assembly (fun i=>g i n) i j 1 1
    let x2 : season p M := fun n l q v=> g true n l q v+g false n l q v
    have hv' : x1 i j=x2 := by
      funext n l q v
      unfold x1 assembly x2
      simp only [one_mul]
      cases i <;> cases j <;> first | rfl | contradiction | exact add_comm _ _
    refine ⟨?_,r,show disappearing U x2 r from hv' ▸ (show disappearing U (x1 i j) r from hg)⟩
    cases i <;> cases j <;> first | contradiction | exact h | exact h.symm
  have hm := census_match ht
  by_cases he : modest U g α true
  · have hh (i : Bool) : modest U g α i := by cases i; exact hm.mp he; exact he
    simp [hh]
  have hh (i: Bool) : ¬modest U g α i := by cases i; exact mt hm.mpr he; exact he
  simp only [census, ite_eq_right (hh _), ite_eq_left ht]; simp [hh]

private theorem eventual_echoes (i j : Bool) (s t r : F) :
    ∃ τ:ℝ,0<τ ∧ ∀ᶠ n in U,
    s*firstBit α i=t*firstBit α j →
      ((∀ l q,tabRef p l q (assembly (fun i=> g i n) i j s t) r ≤ τ) →
        (census U g α).echoes i j s t) := by
  classical
  by_cases hf : disappearing U (fun n=>assembly (fun i=>g i n) i j s t) r
  · exact ⟨1,zero_lt_one,.of_forall (fun _ h _=> census_echoes i j s t r h hf)⟩
  unfold disappearing slight at hf
  push Not at hf
  obtain ⟨l,q,τ,hτ,h⟩:=hf
  exact ⟨τ,hτ,h.mono fun i hi _ H=>(hi.not_ge (H l q)).elim⟩

theorem examine (U : Ultrafilter ℕ) (p : Shape) (M : ℕ) (g : Bool→ season p M) (α : Party) :
    ∃ (c : PredictionClass) (τ : ℝ),0 < τ ∧
       (∀ᶠ n in U,c.recital p (fun i=>g i n) α τ) ∧ c.lit α ∧
       (c=dusk → ∀ i, ∃ r,disappearing U (g i) r) := by
  classical
  let A:=Bool × Bool × (F×F×F)
  let c:= census U g α
  choose τ hτ hg using fun x : A=> @eventual_echoes p U M g α
    x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2
  have hh : ∃ δ:ℝ,0<δ∧∀ x,δ≤τ x := by
    let S := univ.image τ
    have hn : S.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
    refine ⟨S.min' hn, ?_, fun x=> Finset.min'_le _ _ (mem_image_of_mem _ (mem_univ _))⟩
    obtain ⟨x,hx,hx'⟩:= mem_image.mp (Finset.min'_mem _ hn)
    exact hx' ▸ hτ x
  obtain ⟨δ,hδ,hT⟩:=hh
  refine ⟨c,δ,hδ,?_,census_lit,fun h i=>?_⟩
  · filter_upwards [eventually_all.mpr hg] with n h
    refine ⟨census_lit,fun i j s t r he hh=>?_⟩
    exact h (i,j,s,t,r) he (fun l q=>(hh l q).trans (hT _))
  have he : ¬ c.active i := by rw [h]; exact not_false
  exact (show modest U g α i from not_not.mp (fun h=>he ((census_active i).mpr h))).2
end PredictionClass
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PhaseClassCompatibility
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

theorem dusk_lit (α : Party) (h : dusk.lit α) : ∀ i,α i = 1 := fun i=>by
  have hh : 1+α i=0 := h.1 i not_false
  exact add_left_cancel (hh.trans (char_two 1).symm)
end PredictionClass

open PredictionClass

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PreliminaryRestrictions
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

set_option maxHeartbeats 1200000 in
theorem cohort (m : Mixer p n) (w : Wgt (UnitType p n N)) (s : LeafMixture p n N)
    (hs : q.entered p N m w s) (hw : IsLaw w) {ε : ℝ}
    (h : q.predicts p N m s w ε) :
    ∃ (z : Banners) (i : Sage p n N), (∀ x j,totalRank (i.m x j)≤q.e) ∧
      crowdSeed ≤ pr (s.sap w) (tender i q m s z ε) := by
  classical
  let v:=s.sap w
  have hv := LeafMixture.sapLaw (lt_of_lt_of_le (by norm_num) hs.weight) hw
  obtain ⟨g,hg⟩:=h
  let P (x : UnitType p n N) := ∃ z L α, q.seems p m s x g z L α ε
  let Q x:= v x≠ 0∧P x
  have ht : pr v Q=pr v P := avg_congr fun x h=> (by change ind (v x≠0∧P x)=ind (P x); rw [show (v x≠0∧P x)=(P x) from propext (and_iff_right h)])
  choose f hf using show
    ∀ x : UnitType p n N,∃ (z : Bool→Profile p n) (L : Bool→Finset (Label p.b))
      (α : Party), (∀ j,totalRank (z j)≤ q.e) ∧ (Q x → q.seems p m s x g z L α ε) from by
    intro x; by_cases h : Q x
    · obtain ⟨z,L,a,hv⟩:=h.2
      refine ⟨z,L,a,fun i=>?_,fun _=>hv⟩
      exact (effective_rank (hv.1 i).2).trans (LeafMixture.root_bound hs.strength _)
    refine ⟨0,fun _=>∅,0,fun i=>?_,fun he=>(h he).elim⟩
    unfold totalRank
    have hh (j:Comp p.g) :
        ((0:Profile p n) j).rank=0 := Matrix.rank_zero
    exact le_trans (Finset.sum_eq_zero (fun i _=>hh i)).le (Nat.zero_le _)
  choose L a hA hh using hf
  let i:= (⟨g,f,L⟩: Sage p n N)
  have he x (h : Q x) : ∃ z : Banners,tender i q m s z ε x := by
    refine ⟨(a x,glint p (i.m x),decide (delta i.m x=0)),hh x h,rfl,?_⟩
    simp
  have ht' : (0.000001:ℝ) ≤ ∑ j : Banners,pr v (tender i q m s j ε) :=
    hg.trans ((ht.symm ▸ pr_mono hv.nz he).trans (pr_exists_le hv.nz _))
  have hz : ∃ j : Banners,crowdSeed ≤ pr v (tender i q m s j ε) := by
    by_contra! h
    have hx : 0.000001≤∑ _j : Banners,crowdSeed :=
      ht'.trans (Finset.sum_le_sum fun j _=>(h j).le)
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hx
    simp [Banners,Party,F,Vec,ZMod.card] at hx
    norm_num [crowdSeed,pollen] at hx
  obtain ⟨j,hj⟩:=hz
  exact ⟨j,i,hA,hj⟩

set_option maxHeartbeats 1800000 in
theorem pruneWhisper (hl : (U:Filter ℕ)≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in U,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in U,q.entered p (M*n) (m n) (w n) (s n))
    (hc : b.c=dusk)
    (hf : ledger b (U:Filter ℕ))
    (hg : ∀ i,∃ r, disappearing U (b.g i) r)
    (h : ∀ᶠ n in U, crowdSeed ≤ pr ((s n).sap (w n)) (P n) ∧
       ∀ x,P n x → q.seems p (m n) (s n) x (fun i=>b.g i n) (b.m n x) (b.L n x) b.α (b.ε n)) :
    ∃ Q:Campaign p M,∀ᶠ n in U, pollen ≤ pr ((s n).sap (w n)) (Q n) ∧
       ∀ x,Q n x→P n x∧exactInk p (m n) (b.m n) x := by
  classical
  have ha : ∀ i,b.α i=1 := dusk_lit _ (hc ▸ hf.light)
  choose g hG using hg
  let Y (n) (x : UnitType p n (M*n)) i := whisper p (b.g i n) (g i) (onSide x i)
  let Q : Campaign p M := fun n x=>P n x∧∀ i,Y n x i
  have he :
      ∀ᶠ n in U,∀ (i : Bool) (l : Tag p.g) (b':F),tabRef p l b' (b.g i n) (g i) ≤1/100 :=
    eventually_all.mpr fun i=> eventually_all.mpr fun l=> eventually_all.mpr fun b'=> hG i l b'
      _ (by norm_num)
  have hz :
      ∀ᶠ n : ℕ in atTop, (2:ℝ)*(2*q.L*bp (-(1/16:ℝ)*n))≤pollen := by
    have hh : Tendsto (fun n:ℕ=>(2:ℝ)*(2*q.L*bp (-(1/16:ℝ)*n))) atTop (𝓝 0) := by
      have h := ((bp_nat_vanish (by norm_num : 0<(1/16:ℝ))).const_mul (2*q.L)).const_mul 2
      simpa using h
    exact (hh.eventually (gt_mem_nhds pollen_pos)).mono (fun _ hi=>hi.le)
  refine ⟨Q,?_⟩
  filter_upwards [hw,hx,h,hq.wrap.filter_mono hl,he,hf.small (1/16) (by norm_num),
    (hushCalendar p M hq.hM hq.hG hq.hR hq.hJ).filter_mono hl,hz.filter_mono hl,
    (eventually_ge_atTop (2*p.r)).filter_mono hl] with n hn ht hs hq' hG hε hh hz hN
  let s':=s n; let w':=w n
  let v:=s'.sap w'
  have hv : IsLaw v:= LeafMixture.sapLaw (lt_of_lt_of_le (by norm_num) ht.weight) hn.law
  have hS : bySide p v (m n) (2*q.L) := by
    refine LeafMixture.upperSide hn.border (K':=2) (fun x=>?_) (by norm_num) le_rfl
    exact (on_mon hn.law.nz (by norm_num) ht.weight x).trans_eq (by norm_num)
  constructor
  · let V (x : UnitType p n (M*n)) := ∀ i,Y n x i
    have hT := pr_shield hv.nz (P n) V
    let δ := 2*q.L*bp (-(1/16:ℝ)*n)
    have hi (i:Bool) : pr v (fun x=>¬Y n x i) ≤ δ := by
      let T (o:Orient p n (M*n)) := ¬ whisper p (b.g i n) (g i) o
      let f x:= onSide (x:UnitType p n (M*n)) i
      change pr v (fun x=>T (f x)) ≤ _
      rw [←mapW_pr]
      apply (pr_cap (hS i) T).trans
      exact mul_le_mul_of_nonneg_left (hh (m n) hq'.1 _ _ (hG i))
        (mul_nonneg (by norm_num) hq.early.hL)
    have hf : pr v (fun x=>¬V x)≤pollen := by
      refine le_trans ?_ hz
      calc pr v (fun x=>¬V x)
        _ ≤ ∑ i:Bool,pr v (fun x=>¬Y n x i) :=
          (pr_mono hv.nz (p:=fun x=>¬V x) (fun x h => show ∃ i:Bool,¬Y n x i from not_forall.mp h)).trans
            (pr_exists_le hv.nz _)
        _ ≤ 2*δ := by rw [Fintype.sum_bool,two_mul]; exact add_le_add (hi _) (hi _)
    have hh : 2*pollen ≤ pr v (P n) := hs.1
    exact le_trans (by linarith only [hh,hf]) hT
  · intro x hh
    have hs := hs.2 x hh.1
    refine ⟨hh.1,fun i=>?_⟩
    have hi :
        postulates p (onSide x i) (b.g i n) (yoke p (m n) x i (b.m n x i) 1) (b.L n x i) (1/16) := by
      rw [←ha i]
      exact fun z hz j k=>(hs.2 i z hz j k).trans hε
    have he : (↑(b.L n x i).card:ℝ)<bp ((p.b:ℝ)-2*p.j) :=
      lt_of_le_of_lt (by exact_mod_cast (hs.1 i).1) hq.hB
    exact (hush_vat _ _ _ _ (g i) he hi (hh.2 i) hq.hg hq.hR hN).2

set_option maxHeartbeats 1600000 in
theorem outlook_to_dose_oai (hl : (U:Filter ℕ)≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in U,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in U,q.entered p (M*n) (m n) (w n) (s n))
    (h : q.outlook (U:Filter ℕ) p M m w s) :
    ∃ (b : Sketch p M) (P : Campaign p M) (i : Bool), q.dosed (U:Filter ℕ) p M m w s b P ∧
       ∀ᶠ n in U, ∀ x,P n x → ((i=true) ↔ delta (b.m n) x=0) := by
  classical
  obtain ⟨ε,hε,h⟩:=h
  let R (n : ℕ) (z : Banners) (i : Sage p n (M*n)) :=
    (∀ x j,totalRank (i.m x j)≤q.e) ∧ crowdSeed≤pr ((s n).sap (w n)) (tender i q (m n) (s n) z (ε n))
  have hh : ∀ᶠ n in U,∃ (z:Banners) (i:Sage p n (M*n)),R n z i := by
    filter_upwards [h,hw,hx] with n hn ht hv
    exact cohort (m n) (w n) (s n) hv ht.law hn
  obtain ⟨z,hz⟩ := Ultrafilter.eventually_exists_iff.mp hh
  obtain ⟨i,hi⟩ := taking hz
  let g (j:Bool): season p M := fun n => (i n).g j
  obtain ⟨c,τ,hτ,hG,hL,hB⟩:= examine U p M g z.1
  let b:= (⟨c,z.1,z.2.1,fun n=>(i n).m,fun n=>(i n).L,g,ε⟩: Sketch p M)
  let P : Campaign p M := fun n => tender (i n) q (m n) (s n) z (ε n)
  have hT : ledger b (U:Filter ℕ):= ⟨hε,⟨τ,hτ,hG⟩,hL⟩
  have hk :
      ∃ Q : Campaign p M,∀ᶠ n in U, pollen ≤ pr ((s n).sap (w n)) (Q n) ∧
       ∀ x,Q n x→ P n x∧ (b.c=dusk→exactInk p (m n) (b.m n) x) := by
    by_cases hC : c=dusk
    · obtain ⟨Q,hQ⟩:= pruneWhisper hl hq hw hx (show b.c=dusk from hC) hT (hB hC)
       (P:=P) (hi.mono fun n hn=>⟨hn.2,fun x h=>h.1⟩)
      exact ⟨Q,hQ.mono (fun n hn=>⟨hn.1,fun i h=>⟨(hn.2 i h).1,fun _=>(hn.2 i h).2⟩⟩)⟩
    exact ⟨P,hi.mono (fun n hn=>⟨le_trans (show pollen ≤ crowdSeed from
      by unfold crowdSeed; linarith only [pollen_pos]) hn.2,fun x h=>⟨h,fun hh=>(hC hh).elim⟩⟩)⟩
  obtain ⟨Q,hQ⟩:=hk
  have hB : ∀ᶠ n in U,pollen ≤ pr ((s n).sap (w n)) (Q n) := hQ.mono fun i hi=>hi.1
  have hc : q.citable (U:Filter ℕ) p M m w s b Q := by
    refine ⟨(warm.const (trend_sizes (U:Filter ℕ) hl hq.hM).2 pollen_pos).mono hB,hT,?_⟩
    filter_upwards [hQ] with n hn
    intro i hi x hx hp
    obtain ⟨⟨hr,hv,_⟩,hs⟩:= hn.2 x hp
    exact ⟨hr,hv,hs⟩
  refine ⟨b,Q,z.2.2,⟨hc,hB,hi.mono (fun i hi=>hi.1)⟩, hQ.mono fun i hi x hx=>?_⟩
  exact ((hi.2 x hx).1).2.2

end PreparationParameters
end HadwigerCounterexample

end

end OAI
end

theorem solution : type_of% @OAI.HadwigerCounterexample.PreparationParameters.outlook_to_dose_oai := @OAI.HadwigerCounterexample.PreparationParameters.outlook_to_dose_oai
