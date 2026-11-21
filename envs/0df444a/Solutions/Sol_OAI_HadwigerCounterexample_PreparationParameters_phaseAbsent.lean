-- Prove2me | solution 1 for OAI.HadwigerCounterexample.PreparationParameters.phaseAbsent
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T23:05:58.675332+00:00
-- url     : https://prove2.me/submissions/4a267994-3f7f-4799-bd82-3645a6749a84

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
theorem odd_smul_bit {n : ℕ} (hn : Odd n) (x : F) : n • x = x := by
  obtain ⟨m,rfl⟩ := hn
  rw [add_smul, one_smul, mul_smul, two_smul,char_two,zero_add]

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

theorem not_allowed (d : Tag g) : ¬allowed d d := by
  have : NeZero g := ⟨by have := d.isLt; omega⟩
  simp [allowed]

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
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
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

variable {p}

theorem Wstar_le_tag (l : Tag p.g) : Wstar p n ≤ Wtag p n l :=
  Submodule.span_mono (by rintro m ⟨s,z,h,rfl⟩; exact ⟨s,z,fun d t _ => h d t,rfl⟩)
theorem Wtag_le (l : Tag p.g) : Wtag p n l ≤ Wspace p n :=
  Submodule.span_mono (by rintro m ⟨s,z,h,rfl⟩; exact ⟨s,z,rfl⟩)

theorem Wspace_sym {m : Moment p n} (h : m ∈ Wspace p n) : mᵀ = m := by
  unfold Wspace at h
  induction h using Submodule.span_induction with
  | mem m hm => obtain ⟨s,z,rfl⟩ := hm; rw [mom,transpose_vecMulVec]
  | zero => simp
  | add x y _ _ hx hy => rw [transpose_add,hx,hy]
  | smul b x _ hx => rw [transpose_smul,hx]

theorem getPair_edge (l d : Tag p.g) (h : l ≠ d) (x : Profile p n) :
    getPair p n l d x = x (edge l d h) := by rw [getPair,dite_eq_left h]; rfl

theorem getPair_cut (w : Tag p.g → Moment p n) (l d : Tag p.g) :
    getPair p n l d (cut p n w) = w l + w d := by
  by_cases h : l = d
  · subst l; rw [getPair,dite_eq_right, LinearMap.zero_apply,char_two]; simp
  · rw [getPair_edge _ _ h]
    change w _ + w _ = _
    rcases lt_or_gt_of_ne h with e|e
    · rw [edge_eq e]
    · rw [edge_symm,edge_eq e,add_comm]

theorem atom_def (l : Tag p.g) (s : Label p.b) (z : Base p.g n) (e) :
    atom p l s z e = if inc e l then mom p s z else 0 := by
  change (Pi.single l (mom p s z) : Tag p.g → Moment p n) e.val.1 +
    (Pi.single l (mom p s z) : Tag p.g → Moment p n) e.val.2 = _
  by_cases h : e.val.1 = l
  · have h' : e.val.2 ≠ l := h ▸ e.property.ne.symm
    rw [Pi.single_eq_of_ne h',ite_eq_left (show inc e l from Or.inl h)]
    rw [h, Pi.single_eq_same,add_zero]
  by_cases h' : e.val.2 = l
  · rw [Pi.single_eq_of_ne h,ite_eq_left (show inc e l from Or.inr h'),h',Pi.single_eq_same,zero_add]
  rw [Pi.single_eq_of_ne h,Pi.single_eq_of_ne h',add_zero,ite_eq_right (by simp [inc,h,h'])]

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
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_MomentLabelSupport
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Moment Label Support -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Finset
open scoped BigOperators
variable {p : Shape} {n k : ℕ}

theorem mrk_sum_le {I J A : Type} [Fintype I] [Fintype J] (s : Finset A) (f : A → Mat I J) :
    (∑ i∈s,f i).rank ≤ ∑ i∈s,(f i).rank := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s h ih =>
    rw [Finset.sum_insert h,Finset.sum_insert h]
    exact le_trans (mrk_add_le _ _) (by gcongr)

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

theorem etab_disabled {n} {l d : Tag p.g} (h : ¬allowed d l) (t : Tag p.g)
    {m : Moment p n} (hm : m ∈ Wtag p n l) :
    etab p n (Block.O d t) m = 0 := by
  unfold Wtag at hm
  induction hm using Submodule.span_induction with
  | mem m hm =>
    obtain ⟨s,z,hz,rfl⟩ := hm
    rw [mom,etab_point]
    have h' (i : ℕ) : readBit z (Block.O d t) i = 0 := by
      simp [readBit,hz d t h]
    simp only [test,h',mul_zero,Finset.sum_const_zero]
  | zero => rw [map_zero]
  | add _ _ _ _ h g => rw [map_add,h,g,add_zero]
  | smul _ _ _ h => rw [map_smul,h,smul_zero]

theorem roleT_cut {n} (t : Tag p.g) (w : Tag p.g → Moment p n)
    (hw : ∀ i, w i ∈ Wtag p n i) :
    roleT p n t (cut p n w) =
      ∑ (l : Tag p.g), ∑ (d : Tag p.g), etab p n (Block.O d t) (w l) := by
  simp only [roleT,LinearMap.sum_apply,LinearMap.comp_apply,getPair_cut,map_add]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases h : allowed d l
  · rw [ite_eq_left h,etab_disabled p (not_allowed d) t (hw d),add_zero]
  · rw [ite_eq_right h,etab_disabled p h t (hw l)]

theorem role_cut {n} (w : Tag p.g → Moment p n) (hw : ∀ i,w i ∈ Wtag p n i) :
    role p n (cut p n w) = ∑ i, etaO p n (w i) := by
  simp only [role,LinearMap.sum_apply,roleT_cut _ _ _ hw]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  simp only [etaO,LinearMap.sum_apply]

theorem sharedT_cut {n} (hg : Odd p.g) (t : Tag p.g) (w : Tag p.g → Moment p n) :
    sharedT p n t (cut p n w) =
      (∑ i, etab p n Block.S (w i)) + etab p n Block.S (w t) := by
  simp only [sharedT,LinearMap.sum_apply,LinearMap.comp_apply,getPair_cut,map_add,
    Finset.sum_add_distrib,Finset.sum_const, Finset.card_univ]
  simp [Tag,odd_smul_bit hg]

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

variable {ι : Type*} {l : Filter ι} {n f g : ι → ℝ}

namespace ExpSmall

theorem mul (hf : ExpSmall l n f) (hg : ExpO l n g) :
    ExpSmall l n (fun i => f i*g i) := by
  obtain ⟨c,hc,h⟩ := hf
  refine ⟨c/2,by linarith,?_⟩
  filter_upwards [h,hg (c/2) (by linarith)] with i hi hj
  rw [abs_mul, show -(c/2)*n i = -c*n i + c/2*n i by ring, bp_add]
  exact mul_le_mul hi hj (abs_nonneg _) (bp_pos _).le

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
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SparseCutProfiles
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.flipZ_flip _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.reciprocal_actual _root_.OAI.HadwigerCounterexample.reciprocal_twice _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sparse Cut Profiles -/

noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators

variable {p : Shape} {n : ℕ}

theorem Wtag_disabled {l d : Tag p.g} (h : ¬allowed d l) (t : Tag p.g) (i : Fin n)
    {m : Moment p n} (hm : m ∈ Wtag p n l) (s : SelIdx p.b p.j) (r : Row p n) :
    m (s,some (Block.O d t,i)) r = 0 := by
  unfold Wtag at hm
  induction hm using Submodule.span_induction with
  | mem m hm =>
    obtain ⟨s,z,hz,rfl⟩ := hm
    change (selV _ _ _ * z _) * _ = 0
    rw [hz d t h,mul_zero,zero_mul]
  | zero => rfl
  | add x y _ _ hx hy => simp only [Matrix.add_apply,hx,hy,add_zero]
  | smul a x _ h => simp only [Matrix.smul_apply,h,smul_zero]

/-- Intersect W_l over a strict majority. Every O coordinate is forced
to zero and projecting onto the shared variables fixes the matrix. -/
theorem Wtag_majority_star {I : Finset (Tag p.g)}
    (hI : p.g < 2 * I.card) {m : Moment p n} (h : ∀ l ∈ I, m ∈ Wtag p n l) :
    m ∈ Wstar p n := by
  classical
  obtain ⟨a,ha⟩ := Finset.card_pos.mp (show 0 < I.card by omega)
  have hm : m ∈ Wspace p n := Wtag_le a (h a ha)
  have hz (s : SelIdx p.b p.j) (i : Fin n) (d t : Tag p.g) (r : Row p n) :
      m (s,some (Block.O d t,i)) r = 0 := by
    obtain ⟨l,hl,hg⟩ : ∃ l ∈ I, ¬allowed d l := by
      by_contra! he
      have hi := @Finset.card_le_card _ I (Finset.univ.filter (allowed d)) (by
        intro l hl; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,he _ hl⟩)
      have hh := card_allowed d
      rw [Fintype.card_subtype] at hh
      have hi' := hi.trans_eq hh
      omega
    exact Wtag_disabled hg _ _ (h _ hl) _ _
  let kB : BaseIdx p.g n → F := fun i => i.1.elim (fun _ => 0) (fun _ => 1)
  let k : Row p n → F := fun i => Option.elim' 1 kB i.2
  let D := Matrix.diagonal k
  let L (z : Base p.g n) := fun i => kB i * z i
  have hL (s z) : D *ᵥ point p s z = point p s (L z) := by
    funext i
    simp only [D,Matrix.mulVec_diagonal]
    rcases i with ⟨s,i⟩
    rcases i with _|i
    · change (1:F)*_ = _
      rw [one_mul]; rfl
    change kB i * (selV _ _ _ * z i) = _ * (kB i * _); rw [mul_left_comm]
  have hx : liftM D D m ∈ Wstar p n := by
    clear h hz
    unfold Wspace at hm
    induction hm using Submodule.span_induction with
    | mem m he =>
      obtain ⟨s,z,rfl⟩ := he
      rw [mom,liftM_outer,hL]
      exact Submodule.subset_span ⟨s,L z,fun d t i => by
        change (0:F)*_=0
        rw [zero_mul],rfl⟩
    | zero => simp only [map_zero,Submodule.zero_mem]
    | add i j _ _ h g => rw [map_add]; exact Submodule.add_mem _ h g
    | smul _ _ _ h => rw [map_smul]; exact Submodule.smul_mem _ _ h
  have hrow (i j) : k i*m i j = m i j := by
    rcases i with ⟨s,_|⟨⟨d,t⟩|a,i⟩⟩
    · exact one_mul _
    · rw [hz]
      simp
    · exact one_mul _
  have hj : liftM D D m = m := by
    ext i j
    simp only [liftM_def,D,Matrix.diagonal_transpose,Matrix.mul_diagonal,Matrix.diagonal_mul,hrow]
    rw [mul_comm]
    have heq : m i j=m j i := congr_fun (congr_fun (Wspace_sym hm) j) i
    rw [heq,hrow]
  rwa [hj] at hx

theorem mem_nonzeroTags (i) (w : Tag p.g → Moment p n) :
    i ∈ nonzeroTags w ↔ w i ≠ 0 := by classical simp [nonzeroTags]

theorem cut_const (w : Tag p.g → Moment p n) (m : Moment p n) :
    cut p n (fun i => w i+m) = cut p n w := by
  funext i
  change w _ + m + (w _ + m) = w _ + w _
  rw [add_add_add_comm, char_two,add_zero]

theorem common_zero {w v : Tag p.g → Moment p n}
    (h : 2*(nonzeroTags w).card < p.g) (g : 2*(nonzeroTags v).card < p.g) :
    ∃ l, w l=0 ∧ v l=0 := by
  classical
  by_contra! hn
  have hu : Finset.univ ⊆ nonzeroTags w ∪ nonzeroTags v := by
    intro i hi
    by_cases h : w i=0
    · exact Finset.mem_union_right _ ((mem_nonzeroTags _ _).mpr (hn i h))
    · exact Finset.mem_union_left _ ((mem_nonzeroTags _ _).mpr h)
  have hx := (Finset.card_le_card hu).trans (Finset.card_union_le _ _)
  simp only [Finset.card_univ, Tag, Fintype.card_fin] at hx
  omega

private theorem nz_rank {I J : Type} [Fintype I] [Fintype J] {M : Mat I J}
    (h : M ≠ 0) : 1 ≤ M.rank := by
  by_contra hg
  have he : colSp M = ⊥ := Submodule.finrank_eq_zero.mp (by
    rw [show Module.finrank F (colSp M)=M.rank from rfl]; omega)
  have hm : M.mulVecLin = 0 := LinearMap.range_eq_bot.mp he
  apply h
  exact coe_mv_inj (J:=J) (show M.mulVecLin=Matrix.mulVecLin 0 by rw [hm,mulVecLin_zero])

theorem few_unequal {w : Tag p.g → Moment p n} :
    ∑ l : Tag p.g, (nonzeroTags (fun d => w d+w l)).card ≤ 2*totalRank (cut p n w) := by
  classical
  let r := fun i => ((cut p n w) i).rank
  have he (l) :
      (nonzeroTags (fun d => w d+w l)).card ≤
        ∑ i : Comp p.g, if inc i l then r i else 0 := by

    let f (i : Tag p.g) := if w i+w l ≠ 0 then (1:ℕ) else 0
    have h :
        (nonzeroTags (fun d => w d+w l)).card = ∑ i : {i : Tag p.g // l ≠ i}, f i := by
      have hh : (nonzeroTags (fun d => w d+w l)).card = ∑ i, f i := by
        unfold nonzeroTags f
        rw [Finset.card_eq_sum_ones,Finset.sum_filter]
      rw [hh,Fintype.sum_eq_add_sum_subtype_ne _ l]
      have hz : f l=0 := by simp [f,char_two]
      rw [hz,zero_add]
      exact (Equiv.subtypeEquivRight (show ∀ x, (x ≠ l) ↔ (l ≠ x) from fun _ => ne_comm)).sum_comp
        (fun x : {i : Tag p.g // l ≠ i} => f x)
    rw [h]
    have h' :
        (∑ i : Comp p.g, if inc i l then r i else 0) = ∑ i : TagStar l, r i.val := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) _
    rw [h',← (starEquiv l).sum_comp]
    refine Finset.sum_le_sum fun i _ => ?_
    unfold f
    split
    · rename_i hx
      change 1 ≤ r (edge l i i.property)
      apply nz_rank
      have h0 := getPair_edge l i i.property (cut p n w)
      rw [getPair_cut, add_comm] at h0
      rw [← h0]
      exact hx
    · exact Nat.zero_le _
  refine (Finset.sum_le_sum (fun i _ => he i)).trans_eq ?_
  unfold totalRank
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : Finset.univ.filter (fun l => inc i l) = {i.val.1,i.val.2} := by
    ext; simp [inc,eq_comm]
  rw [← Finset.sum_filter,hi]
  simp [i.property.ne, two_mul,r]

/-- Sparse representatives: the bound here is g*(number of supported tags)
≤ 2*total rank (apply with total rank ≤ 2D). -/
theorem sparse_rep {x : Profile p n} (h : x ∈ Xspace p n)
    (hg : 4*totalRank x < p.g*p.g) :
    ∃ w : Tag p.g → Moment p n, cut p n w=x ∧
      (∀ l,w l∈Wtag p n l) ∧
      p.g*(nonzeroTags w).card ≤ 2*totalRank x ∧ 2*(nonzeroTags w).card < p.g := by
  classical
  obtain ⟨w,hw,rfl⟩ := mem_X.mp h
  let B := fun l => nonzeroTags (p:=p) (fun i => w i+w l)
  let t := totalRank (cut p n w)
  have hn : 0 < p.g := Nat.pos_of_ne_zero (fun he => by
    have hi : p.g*p.g=0 := by rw [he]
    omega)
  have : NeZero p.g := ⟨hn.ne'⟩
  obtain ⟨l,hl⟩ : ∃ l : Tag p.g, p.g*(B l).card ≤ 2*t := by
    by_contra! he
    have he1 :
        ∑ _l : Tag p.g, 2*t < ∑ l : Tag p.g, p.g*(B l).card :=
      Finset.sum_lt_sum (fun l _ => (he l).le) ⟨0,Finset.mem_univ _,he 0⟩
    simp only [Finset.sum_const,Finset.card_univ,Tag,Fintype.card_fin,nsmul_eq_mul] at he1
    rw [← Finset.mul_sum] at he1
    have hh : p.g*(∑ l, (B l).card) ≤ p.g*(2*t) := Nat.mul_le_mul_left _ few_unequal
    exact Nat.not_lt_of_le hh he1
  let v := fun i => w i+w l
  have hi : 2*(nonzeroTags v).card < p.g := by
    change p.g*(nonzeroTags v).card ≤ _ at hl
    by_contra h1
    have hh : p.g*p.g ≤ p.g*(2*(nonzeroTags v).card) :=
      Nat.mul_le_mul_left _ (Nat.le_of_not_lt h1)
    change 4*t< p.g*p.g at hg
    nlinarith
  refine ⟨v,cut_const w _,fun i => ?_,hl,hi⟩
  refine Submodule.add_mem _ (hw i) ((Wstar_le_tag i) ?_)
  apply Wtag_majority_star (I := (nonzeroTags v)ᶜ)
  · rw [Finset.card_compl,show Fintype.card (Tag p.g)=p.g from Fintype.card_fin _]
    omega
  · intro j hj
    have hh : w j+w l=0 := by
      change v j=0
      have h := Finset.mem_compl.mp hj
      rwa [mem_nonzeroTags, not_not] at h
    have he : w j = w l := add_right_cancel (hh.trans (char_two _).symm)
    rw [← he]; exact hw j

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_TensorIntersections
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
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
theorem colSp_primary (A : Mat U (I⊕J)) : colSp (primary A) ≤ colSp A :=
  calc colSp (primary A) ≤ colSp (primary A) ⊔ colSp (channel A) := le_sup_left
       _ = colSp A := by rw [← colSp_join,fromCols_frame]

omit [Fintype U] in
theorem join_kernel {A : Mat U I} {B : Mat U J}
    (ha : Function.Injective A.mulVec) (hb : Function.Injective B.mulVec) :
    dim (colSp A ⊓ colSp B : Submodule _ _) = dim (ker (fromCols A B).mulVecLin) := by
  have h := finrank_sup_add_finrank_inf_eq (colSp A) (colSp B)
  have h' := (fromCols A B).mulVecLin.finrank_range_add_finrank_ker
  rw [← colSp_join] at h
  change dim (colSp _) + dim _ = dim _+dim _ at h
  change dim (colSp _) + dim _ = dim _ at h'
  rw [colSp_dim A,colSp_dim B,mrk_inj.mp ha,mrk_inj.mp hb] at h
  rw [dim_vec, Fintype.card_sum] at h'
  omega

omit [Fintype U] in
theorem colSp_lift_le (P : Mat U I) (Q : Mat L J) (A : Mat I J) :
    colSp (liftM P Q A) ≤ colSp P := by
  rw [liftM_def,Matrix.mul_assoc,colSp, Matrix.mulVecLin_mul]
  exact LinearMap.range_comp_le_range _ _

omit [Fintype U] in
theorem rank_lift_le (P : Mat U I) (Q : Mat L J) (A : Mat I J) :
    (liftM P Q A).rank ≤ A.rank :=
  (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

theorem rank_lift_eq {P : Mat U I} {Q : Mat L J} (hP : Function.Injective P.mulVec)
    (hQ : Function.Injective Q.mulVec) (A : Mat I J) :
    (liftM P Q A).rank = A.rank := by
  classical
  obtain ⟨P',h1⟩ := mat_left_inv hP
  obtain ⟨Q',h2⟩ := mat_left_inv hQ
  refine le_antisymm (rank_lift_le P Q A) ?_
  have h := rank_lift_le P' Q' (liftM P Q A)
  rw [liftM_comp,h1,h2,liftM_def,Matrix.one_mul,Matrix.transpose_one,Matrix.mul_one] at h
  exact h

end Rank

theorem totalRank_shared {m : Mixer p n} {x y : Orient p n N}
    (hx : frameLaw m x) (hy : frameLaw m y) {v w : Profile p n}
    (h : Uembed x v = Uembed y w) :
    totalRank v = totalRank w ∧ totalRank v ≤ joins (x,y) := by
  have he (x : Orient p n N) (hx : frameLaw m x) (a : Profile p n) (i) :
      (Uembed x a i).rank = (a i).rank :=
    rank_lift_eq (primary_inj (hx i).1) (primary_inj (hx i).2.1) (a i)
  have hf i : (v i).rank=(w i).rank := by rw [← he x hx,← he y hy,h]
  refine ⟨Finset.sum_congr rfl fun i _ => hf i, Finset.sum_le_sum fun i _ => ?_⟩
  let A := (x i).1
  let B := (y i).1
  have hi (x : Orient p n N) (v) :
      colSp (Uembed x v i) ≤ colSp (x i).1 :=
    (colSp_lift_le _ _ _).trans (colSp_primary _)
  have hh : colSp (Uembed x v i) ≤ colSp A ⊓ colSp B :=
    le_inf (hi x v) (by rw [h]; exact hi y w)
  change (v i).rank ≤ dim (ker (images _ _).mulVecLin)
  rw [← he x hx,← colSp_dim]
  apply le_trans (Submodule.finrank_mono hh)
  exact (join_kernel (hx i).1 (hy i).1).le

theorem eta_share {m : Mixer p n} {x : Orient p n N} {v : Profile p n} (hj : 1 ≤ p.j)
    (hx : frameLaw m x) (hv : v ∈ Xspace p n) (i) :
    mpair (1:Mat (Fin N) (Fin N)) (Uembed x v i) = eta p n (v i) := by
  let P := primary (x i).1
  let Q := primary (x i).2
  have hi : v i ∈ Wspace p n := by
    obtain ⟨w,hw,rfl⟩ := mem_X.mp hv
    exact Submodule.add_mem _ (Wtag_le _ (hw _)) (Wtag_le _ (hw _))
  change mpair _ (liftM P Q (v i)) = _
  rw [mpair_liftM,liftM_def,transpose_transpose, Matrix.mul_one,
    show Pᵀ*Q=selfM p n m.mixM from (hx i).2.2.1,selfM_pair _ hj _ hi]

theorem parityW_shared {m : Mixer p n} (hj : 1 ≤ p.j) {x y : Orient p n N}
    (hx : frameLaw m x) (hy : frameLaw m y) {v w : Tag p.g → Moment p n}
    (hv : ∀ l, v l∈ Wtag p n l) (hw : ∀ l, w l∈ Wtag p n l)
    (h : Uembed x (cut p n v) = Uembed y (cut p n w))
    (hv' : 2 * (nonzeroTags v).card < p.g)
    (hw' : 2 * (nonzeroTags w).card < p.g) : parityW v = parityW w := by
  have he i : eta p n (cut p n v i) = eta p n (cut p n w i) := by
    rw [← eta_share hj hx (mem_X.mpr ⟨v,hv,rfl⟩),← eta_share hj hy (mem_X.mpr ⟨w,hw,rfl⟩),h]
  obtain ⟨l,hl,hL⟩ := common_zero hv' hw'
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases htl : l=t
  · subst t; rw [hl,hL]
  have hf (w : Tag p.g → Moment p n) (h : w l=0) :
      cut p n w (edge l t htl) = w t := by
    rw [← getPair_edge l t htl (cut p n w), getPair_cut,h,zero_add]
  exact (by simpa only [hf v hl,hf w hL] using he (edge l t htl))

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

theorem evmat_transpose (M : Mat I J) (x : Vec I) (y : Vec J) :
    evmat Mᵀ y x=evmat M x y := dotProduct_transpose_mulVec _ _ _
theorem evmat_pull (P : Mat K I) (Q : Mat L J) (A : Mat K L) (x : Vec I) (y : Vec J) :
    evmat (pullM P Q A) x y=evmat A (P *ᵥ x) (Q *ᵥ y) := by
  rw [←mpair_outer,←mpair_outer,← liftM_outer,mpair_liftM]; rfl

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

theorem keep_o {f : Flavor g} {x : Tag g} {i j}
    (h : keeps f x (Block.O i j)) : allowed i x := by
  rcases f with (_|_|_) <;> simp [keeps] at h
  · exact h
  exact h.1

theorem keepZ (f : Flavor g) (x : Tag g) : keeps f x Block.Z := by
  rcases f with (_|_|_) <;> simp [keeps]

end Flavor

theorem lit_allows (f : Flavor g) (x : Tag g) (y : Knobs g n) :
    allows x (lit f x y) :=
  fun _ _ h _ => ite_eq_right (fun g => h (Flavor.keep_o g))

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

theorem role_scan (p : Shape) {n} (l s f) (x : Knobs p.g n) :
    role p n (useAtom p l s f x)=(scan p l f x).diagO := by
  unfold Digest.diagO useAtom atom
  let M := mom p s (lit f l x)
  have h (i : Tag p.g) :
      (Pi.single l M : Tag p.g → Moment p n) i∈Wtag p n i := by
    by_cases h : i=l
    · subst i; rw [Pi.single_eq_same]
      exact Submodule.subset_span ⟨_,_,lit_allows f l x,rfl⟩
    simp [h]
  rw [role_cut _ _ h,Finset.sum_eq_single l]
  · rw [Pi.single_eq_same,etaO,LinearMap.sum_apply]
    simp_rw [LinearMap.sum_apply,scan_is p l s]
    rfl
  · intro i _ hi; simp [hi]
  simp

theorem spins_law (p : Shape) (n : ℕ) : IsLaw (spins p n) := draws_law unif_law

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

omit [Fintype B] [DecidableEq J] in
theorem draw_elem {p : Wgt B} (x : J→B) (i : J)
    (h : draws J p x≠0) : p (x i)≠0 := fun hx => h (prod_eq_zero (mem_univ _) hx)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_MixerConditions
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.flipZ_flip _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.reciprocal_actual _root_.OAI.HadwigerCounterexample.reciprocal_twice _root_.OAI.HadwigerCounterexample.wsign_abs _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mixer Conditions -/

noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators
variable {p : Shape} {n : ℕ}

theorem Tmix_atom (m : Mixer p n) (x : Profile p n) (s : Label p.b)
    (z : Base p.g n) (l : Tag p.g) :
    Tmix m x (atom p l s z)=mpair (qmix m x l) (mom p s z) := by
  classical
  let v (i) := atom p l s z i
  let q := mom p s z
  have h (f : Comp p.g → Moment p n →ₗ[F] F) :
      ∑ e, f e (v e) = ∑ e : TagStar l, f e.val q := by
    let g e := f e q
    have he :
        ∑ e, f e (v e) = ∑ e ∈ Finset.univ.filter (fun e => inc e l),g e := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold v
      by_cases h : inc i l <;> simp [atom_def,h,q,g]
    rw [he]
    exact Finset.sum_subtype _ (by simp) g
  let L j a b := liftM (m.mixL j a b) (m.mixR j a b)
  let R j a b := liftM (m.mixL j a b)ᵀ (m.mixR j a b)ᵀ
  have hh (j : Fin p.J) :
      ∑ e, ∑ f, mpair (x e) (L j e f (v f)) =
        ∑ f : TagStar l, ∑ e, mpair (R j e f.val (x e)) q := by
    have he (e : Comp p.g) (f) : mpair (x e) (L j e f (v f)) =
          mpair (R j e f (x e)) (v f) := mpair_liftM _ _ _ _
    simp_rw [he]
    rw [Finset.sum_comm]
    let F f := ∑ e, mpair (R j e f (x e))
    specialize h F
    simpa only [F,LinearMap.sum_apply] using h
  have hh' (j : Fin p.J) :
      ∑ f, ∑ e, mpair (v f) (L j f e (x e)) =
        ∑ f : TagStar l, ∑ e, mpair (L j f.val e (x e)) q := by
    have he (e f : Comp p.g) : mpair (v f) (L j f e (x e))=mpair (L j f e (x e)) (v f) :=
      mpair_comm _ _
    simp_rw [he]
    let F f := ∑ e, mpair (L j f e (x e))
    specialize h F
    simpa only [F,LinearMap.sum_apply] using h
  change (∑ j, ∑ e, ∑ f, mpair (x e) (L j e f (v f)))+
    (∑ j, ∑ f, ∑ e,mpair (v f) (L j f e (x e))) = _
  simp_rw [hh,hh']
  simp only [qmix,mpair_sum,mpair_add,Finset.sum_add_distrib]
  rfl

theorem qmix_rank (m : Mixer p n) (x : Profile p n) (l) :
    (qmix m x l).rank ≤ p.J*(p.g-1)*(2*totalRank x) := by
  let W := 2*totalRank x
  let F (j : Fin p.J) (f : TagStar l) (e : Comp p.g) :=
    liftM (m.mixL j e f.val)ᵀ (m.mixR j e f.val)ᵀ (x e)+
    liftM (m.mixL j f.val e) (m.mixR j f.val e) (x e)
  have hh (j : Fin p.J) (f : TagStar l) : (∑ e, F j f e).rank ≤ W := by
    have hi (e : Comp p.g) : (F j f e).rank ≤ 2*(x e).rank := by
      unfold F; rw [two_mul]
      exact (mrk_add_le ..).trans (Nat.add_le_add (rank_lift_le ..) (rank_lift_le ..))
    refine (mrk_sum_le Finset.univ _).trans ((Finset.sum_le_sum fun i _ => hi i).trans_eq ?_)
    rw [←Finset.mul_sum]; rfl
  have hj j :
      (∑ f : TagStar l,∑ e,F j f e).rank ≤ (p.g-1)*W := by
    refine (mrk_sum_le Finset.univ _).trans ((Finset.sum_le_sum fun i _ => hh j i).trans_eq ?_)
    simp only [Finset.sum_const,Finset.card_univ,card_star,nsmul_eq_mul] <;> simp
  refine (mrk_sum_le Finset.univ _).trans ((Finset.sum_le_sum fun i _ => hj i).trans_eq ?_)
  simp [W,mul_assoc]

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

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_QueryConcentration
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
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

theorem avg_cross_sq (w : Wgt A) (f : Wgt A) :
    avg w f ^ 2=avg (draws Bool w) (fun q => f (q true)* f (q false)) := by
  let g (i : Bool) := f
  have hh := prodW_avg (fun _ : Bool => w) g
  have he : prodW g=(fun q => f (q true)* f (q false)) := by ext; unfold prodW; rw [Fintype.prod_bool]
  rw [he,Fintype.prod_bool] at hh; rw [pow_two]; exact hh.symm

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

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_TesterFourierSupport
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Tester Fourier Support -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Submodule Function LinearMap Finset
open scoped BigOperators
variable {p : Shape} {n : ℕ}

theorem roleT_scan (p : Shape) (i l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (x : Knobs p.g n) :
    roleT p n i (useAtom p l s f x) = ∑ d:Tag p.g,scan p l f x (.inl (d,i)) := by
  classical
  unfold useAtom atom
  let M := mom p s (lit f l x)
  have h (t : Tag p.g) : (Pi.single l M : Tag p.g→ Moment p n) t ∈Wtag p n t := by
    by_cases ht : t=l
    · subst t; rw [Pi.single_eq_same]; exact Submodule.subset_span ⟨_,_,lit_allows f l x,rfl⟩
    simp [ht]
  rw [roleT_cut p i _ h,Finset.sum_eq_single l,Pi.single_eq_same]
  · simp_rw [scan_is p l s]; rfl
  · intro i _ hi; simp [hi]
  simp

theorem sharedT_scan (p : Shape) (hg : Odd p.g) (i l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (x : Knobs p.g n) :
    let r := scan p l f x (.inr ())
    sharedT p n i (useAtom p l s f x)= r+(if l=i then r else 0) := by
  classical
  intro r
  unfold r useAtom atom
  rw [sharedT_cut _ hg,Finset.sum_eq_single l]
  · rw [Pi.single_eq_same,scan_is p l s f]; by_cases h : i=l <;> simp [h,asBlock,Ne.symm]
  · intro i _ hi; simp [hi]
  simp

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

theorem atom_union (p : Shape) (n : ℕ) (z : Base p.g n) (s : Label p.b) :
    ∑ i:Tag p.g,atom p i s z=0 := by
  simp_rw [atom,←map_sum (cut p n)]
  rw [Finset.univ_sum_single (fun i : Tag p.g => mom p s z)]
  funext x
  exact char_two (mom p s z)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SyntheticSliceExperiments
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Synthetic Slice Experiments -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Function Finset
open scoped BigOperators
variable {p : Shape} {n : ℕ}

theorem ticketsFee_pos (p : Shape) : 0<ticketsFee p := by unfold ticketsFee; positivity
set_option maxHeartbeats 800000 in
theorem rungPrice (n : ℕ) (w : Tickets p) (h : 2*p.r≤n) :
    pr (spins p n) (issued p w)=ticketsFee p := by
  classical
  have he i : gaugeAddr p i<n := by
    rcases i with ⟨⟨i,j⟩,b⟩
    have := j.isLt
    cases b <;> simp only [gaugeAddr]
    all_goals
      simp
      omega
  let g : Gauge p → BaseIdx p.g n := fun i => (asBlock i.1.1,⟨gaugeAddr p i,he i⟩)
  have hi : Injective g := by
    rintro ⟨⟨i,j⟩,c⟩ ⟨⟨k,l⟩,d⟩ hh
    obtain rfl : i=k := asBlock_inj (congrArg Prod.fst hh)
    have hh := congrArg (fun x : BaseIdx p.g n=>x.2.val) hh
    cases c <;> cases d
    all_goals
      simp only [g,gaugeAddr,Bool.false_eq_true, ↓reduceIte] at hh
      first
      | solve | omega
      | solve | simp [Fin.ext (show j.val=l.val from by omega)]
  let e : Base p.g n≃Knobs p.g n := ⟨curry,uncurry,fun _=>rfl,fun _=>rfl⟩
  have hh (x : Base p.g n) : issued p w (e x)↔ ∀ i,x (g i)=w i := by
    unfold issued
    rw [funext_iff]
    simp only [punchField,zget,dite_eq_left (he _)]
    rfl
  rw [spins,←draws_unif,← unif_equiv e,mapW_pr]
  simp_rw [hh]; rw [draws_unif]
  change pr (prodW (fun (_ : BaseIdx p.g n)=>unif)) _= _
  rw [prodW_pr_inj hi (fun _=>unif_law) (fun i y=>y=w i)]
  simp only [pr_point',unif_apply,F,ZMod.card,ticketsFee]
  simp

theorem ticketLaw (n : ℕ) (w : Tickets p) (h : 2*p.r≤n) : IsLaw (rung p n w) :=
  on_law (spins_law p n).nz ((ticketsFee_pos p).trans_eq (rungPrice n w h).symm)
theorem ticketFlow (n : ℕ) (w : Tickets p) (h : 2*p.r≤n) :
    mapW (rung p n w) (freePart p)=unif := by
  refine fresh_Z p n (issued p w) (fun x y=>?_) (ticketLaw n w h)
  have hi : punchField p (x+Pi.single Block.Z y)=punchField p x := by
    classical
    funext i
    have hh : asBlock i.1.1≠Block.Z := by
      rcases i with ⟨⟨⟨i,j⟩|⟨⟩,b⟩,c⟩ <;> simp [asBlock,Block.O,Block.S,Block.Z]
    unfold punchField; simp only [Pi.add_apply,Pi.single_eq_of_ne hh,add_zero]
  unfold issued; rw [hi]
theorem ticketCap (n : ℕ) (w : Tickets p) (h : 2*p.r≤n) :
    ∀ x,rung p n w x≤(ticketsFee p)⁻¹ * spins p n x :=
  on_mon (spins_law p n).nz (ticketsFee_pos p) (le_of_eq (Eq.symm (rungPrice n w h)))

theorem tabGram_sound (p : Shape) (n : ℕ) (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (x y : Knobs p.g n) (m : Mixer p n) (hj : 1 ≤ p.j) :
    let E:=selfM p n m.mixM
    evmat E (spring p l s f x) (spring p l s f y)=tabGram p l f (punchField p x)
      (punchField p y) := by
  classical
  intro E
  let z (x : Knobs p.g n) := lit f l x
  let A (B : Block p.g) := test p n B (z x) (z y)
  let h i := usesPunch p l f i
  have hX (i : ProbeIdx p.g) :
      A (asBlock i) = ∑ j : Fin p.r, (fun t:Punch p => if usesPunch p l f t then
        punchField p x (t,true)*punchField p y (t,false) else 0) (i,j) := by
    unfold A test z; refine Finset.sum_congr rfl fun j _=>?_
    let B := asBlock i
    have he (u : Knobs p.g n) (k) :
        readBit (lit f l u) B k=if f.keeps l B then zget (u B) k else 0 := by
      by_cases hh : k<n <;> simp [lit,zget,readBit,hh]
    by_cases ht : f.keeps l B
    · rw [he,he,ite_eq_left ht,ite_eq_left ht]
      exact Eq.symm (ite_eq_left (show usesPunch p l f (i,j) from ht))
    rw [he,he,ite_eq_right ht,ite_eq_right ht,zero_mul]
    exact Eq.symm (ite_eq_right (show ¬usesPunch p l f (i,j) from ht))
  rw [←mpair_outer]; unfold E spring selfM; simp_rw [mpair_add,mpair_sum]
  rw [sharpM_point _ hj]; simp only [char_two,zero_mul,sum_const_zero,add_zero]
  unfold tabGram
  rw [Fintype.sum_prod_type,Fintype.sum_sum_type,Fintype.sum_prod_type]
  simp only [Fintype.sum_unique]

  congr 1
  · refine Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=> ?_
    exact (etab_point p (Block.O i j) ..).trans (hX (.inl (i,j)))
  exact (etab_point p Block.S ..).trans (hX (.inr ()))
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_NominalPointArrays
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nominal Point Arrays -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Function Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I J U : Type} [Fintype I] [Fintype J] [Fintype U]
variable [DecidableEq I] [DecidableEq J] [DecidableEq U]

theorem sketch_law (p : Shape) (n : ℕ) (a : I→ Tickets p) (h : 2*p.r≤n) :
    IsLaw (sketchLaw p n a) := prodW_law (fun _ =>ticketLaw n _ h)

omit [DecidableEq I] in
theorem sketch_matrix (p : Shape) (l s f) (m : Mixer p n) (a : I→ Tickets p)
    (hj : 1 ≤ p.j) (x : I→Knobs p.g n) (h : sketchLaw p n a x ≠0) :
    let A:= incision p l s f x
    pullM A A (selfM p n m.mixM)= Matrix.of (fun i j=>tabGram p l f (a i) (a j)) := by
  classical
  intro A
  have he i : punchField p (x i)=a i := by
    by_contra! hv
    refine h (Finset.prod_eq_zero (mem_univ i) (f:=fun i=>rung p n (a i) (x i)) ?_)
    unfold rung; rw [onW_val,ind_zero (show ¬ issued p _ _ from hv),mul_zero,zero_div]
  ext i j
  let E := selfM p n m.mixM
  have hi : (pullM A A E) i j=evmat E (spring p l s f (x i)) (spring p l s f (x j)) := by
    rw [pullM_def,Matrix.mul_assoc]; rfl
  rw [hi,tabGram_sound _ n l s f (x i) (x j) m hj,he,he]; rfl

omit [DecidableEq I] in
set_option maxHeartbeats 600000 in
theorem inc_compound (p : Shape) (l s f) (x : I→ Knobs p.g n) (u : Vec I) (h : weightsAff u) :
    incision p l s f x *ᵥ u=spring p l s f (compound p x u) := by
  classical
  funext i
  rcases i with ⟨i,_|k⟩
  · unfold Matrix.mulVec dotProduct incision; simp only [Matrix.of_apply,spring,point_eval]
    change ∑ j,monoBit s i.val*1*_ = monoBit s i.val *1
    rw [← Finset.mul_sum,show ∑ i,u i=1 from h,mul_one]
  unfold Matrix.mulVec dotProduct incision; simp only [Matrix.of_apply,spring,point_eval]
  change ∑ j,monoBit s i.val*lit f l (x j) k*_ = monoBit s i.val* lit f l (compound p x u) k
  have hz :
      lit f l (compound p x u) k=∑ i,u i*lit f l (x i) k := by
    unfold lit compound
    by_cases h : f.keeps l k.1
    · simp only [Finset.sum_apply,ite_eq_left h,Pi.smul_apply,smul_eq_mul]
    simp only [ite_eq_right h,mul_zero,Finset.sum_const_zero]
  rw [hz,Finset.mul_sum]; exact Finset.sum_congr rfl fun i _=> by ring

omit [DecidableEq I] in
theorem inc_diag (p : Shape) (l s f) (m : Mixer p n) (x : I →Knobs p.g n)
    (u : Vec I) (h : weightsAff u) (hj : 1 ≤ p.j) :
    let A:=incision p l s f x; let y:=compound p x u
    evmat (pullM A A (selfM p n m.mixM)) u u=dialed p l f y := by
  intro A y
  rw [evmat_pull,inc_compound p l s f x u h,←mpair_outer]
  exact (selfM_pair p hj _ (show mom p _ (lit f l y)∈ Wspace p n from Submodule.subset_span
    ⟨s,_,rfl⟩)).trans (etaScan p l s f y).symm

theorem labFee_pos (p : Shape) (I : Type) [Fintype I] : 0<labFee p I := pow_pos (ticketsFee_pos _) _

theorem sketch_point (p : Shape) (n : ℕ) (a:I→ Tickets p) (h : 2*p.r≤n)
    (u : Vec I) (he : weightsAff u) (P : Knobs p.g n→Prop) :
    pr (sketchLaw p n a) (fun x=> P (compound p x u)) ≤
      (labFee p I)⁻¹*pr (spins p n) P := by
  classical
  have hh x :
      sketchLaw p n a x≤(labFee p I)⁻¹*unif x := by
    unfold sketchLaw labFee
    rw [draws_unif]
    have hn i : spins p n (x i)=unif (x i) := by rw [spins,← draws_unif]
    apply le_trans (Finset.prod_le_prod (fun i (_: i∈(univ:Finset I)) => (ticketLaw n _ h).nz
      (x i)) (fun i _=>(ticketCap n (a i) h (x i))))
    simp_rw [Finset.prod_mul_distrib,hn]
    simp only [Finset.prod_const, card_univ, inv_pow]
    exact le_rfl
  have hs : Surjective (compoundAll p n u) := by
    intro x
    refine ⟨fun y => x,?_⟩
    change ∑ i,u i • x=x
    rw [← Finset.sum_smul,show ∑ i,u i=1 from he,one_smul]
  have ht :
       pr unif (fun x => P (compound p x u))=pr (spins p n) P := by
    unfold spins
    rw [← draws_unif]
    change pr unif (fun x=>P (compoundAll p n u x))=_
    rw [← mapW_pr,map_unif_surjective _ hs]
  exact (pr_cap hh _).trans_eq (congrArg _ ht)
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SyntheticSliceComparison
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Synthetic Slice Comparison -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Function Finset
open scoped BigOperators
variable {p : Shape} {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {n N : ℕ}

theorem display_law (p : Shape) (G : Mat I I) (N : ℕ) (hN : 2*num I-(N:ℝ)≤ -1) :
    IsLaw (displayLaw p I N G) := by
  have hU : num I + num I-num (Fin N) ≤ -1 := by
    rw [← two_mul]; simpa only [num,Fintype.card_fin] using hN
  have hh := gram_norm_quarter G hU
  have ht : IsLaw (unifOn (gramGood G (U:=Fin N))) := by
    rw [←on_unif]; exact on_law unif_law.nz ((div_pos (bp_pos _) (by norm_num : 0<(4:ℝ))).trans_le hh)
  exact prodW_law (fun i : Comp p.g => ht)

theorem drill_law (p : Shape) {A : Mat (Row p n) I} (h : Injective A.mulVec)
    (m : Mixer p n) (hN : 2*num (Full p n)<N) :
    mapW (raw m N) (drill p A) = displayLaw p I N (pullM A A (selfM p n m.mixM)) := by
  classical
  unfold raw drill displayLaw
  let w := rawC m N
  have hh := mapW_repeat (fun (_ : Comp p.g)=>w) (fun i=>peer p A A (N:=N))
  rw [peer_cap _ _ hN h h] at hh
  exact hh

omit [DecidableEq I] in
theorem drill_view (p : Shape) {A : Mat (Row p n) I} (o : Orient p n N) :
    drill p A o= relay (Comp p.g) I N
      (peekR p (drStage p I) (drQuery A) (drQuery A) o) := by
  funext i; apply Prod.ext <;> rfl

theorem bloom_incision (p : Shape) (n : ℕ) (x : J→I→ Knobs p.g n)
    (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (h : bloom p x) (a : J) :
    Injective (incision p l s f (x a)).mulVec := by
  classical
  let M := incision p l s f (x a); let T:= freeNet p x
  let g := Prod.mk a (β:=I)
  have he (i : I) (j) : M (emptySel,some (Block.Z,j)) i=T j (g i) := by
    change point _ _ _ _=_
    rw [point_base_eval]
    exact ite_eq_left (Flavor.keepZ ..)
  intro y z hy
  refine inject_column_slice T h (show Injective g from fun i j h=>congrArg Prod.snd h) ?_
  funext i
  have hh:= congr_fun hy (emptySel,some (Block.Z,i))
  change ∑ j:I,M _ _*_=∑ j:I, M _ _*_ at hh
  simp_rw [he] at hh; exact hh
theorem bloom_drill (p : Shape) (n : ℕ) (x : J→I→ Knobs p.g n)
    (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (h : bloom p x) (i : Comp p.g) :
    Injective (pooled (fun j=> drQuery (incision p l s f (x j))) i).mulVec := by
  classical
  let r := fun y : J×(Comp p.g × I)=> (y.1,y.2.2)
  let T := tied (drStage p I) J
  have hr : Injective (fun a : Port T i=> r a.val) := by
    rintro ⟨⟨j,a,c⟩,ha⟩ ⟨⟨j',b,d⟩,hb⟩ hh
    change (j,c)=(j',d) at hh
    cases hh
    cases ha; cases hb; rfl
  refine ray_bloom (b:=r) _ _ h hr ?_
  intro j k
  change point p s (lit f l (x (r j.val).1 (r j.val).2)) (emptySel,some (Block.Z,k))=freeNet p x k (r j.val)
  rw [point_base_eval]; exact ite_eq_left (Flavor.keepZ ..)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_GramArrayConcentration
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gram Array Concentration -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Function Filter
open scoped BigOperators Topology
variable {p : Shape} {I : Type} [Fintype I] [DecidableEq I] {n N : ℕ}

set_option maxHeartbeats 1000000 in
theorem magazine_var (p : Shape) (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (P : Display p I N → Prop) (a : I → Tickets p) (m : Mixer p n)
    (h : 2*num (Full p n)<N) (hj : 1≤p.j) (hn : 2*p.r≤n) (hN : 2*num I-(N:ℝ)≤ -1)
    (k : ℝ) (hk : num (Bool × Comp p.g × I)≤ k) (hK : 2*k-N≤ -1) :
    let g:= tied (drStage p I) Bool
    let V := displayLaw p I N (labGram p l f a)
    avg (raw m N) (fun i => (magazine p l s f P a i - pr V P)^2) ≤
      2 * netFact g * twinkle g k N + bp (num Bool*num I - n) := by
  classical
  let Z := labGram p l f a
  let W := sketchLaw p n a
  let μ := raw m N
  have hw : IsLaw W:= sketch_law p n a hn
  have hμ : IsLaw μ := raw_law m h
  have hs := display_law p Z N hN
  intro g V
  let U i := ind (P i)-pr V P
  have he : avg V U=0 := by unfold U; rw [avg_sub,hs.avg_const]; exact sub_self _
  have hh (i) : |U i| ≤1 := by
    have hl := pr_nonneg (p:=P) hs.nz; have ht := (pr_le_tot (p:=P) hs.nz).trans hs.total.le
    unfold U; rw [abs_le]; constructor <;> linarith only [ind_nonneg (P i),ind_le_one (P i),hl,ht]
  let A (x : I → Knobs p.g n) := incision p l s f x
  let F (i : Orient p n N) x := U (drill p (A x) i)
  have heq (i) :
      magazine p l s f P a i-pr V P = avg W (F i) := by
    unfold F U; rw [avg_sub,hw.avg_const]; rfl
  let w := draws Bool W; have hW : IsLaw w := draws_law hw
  let E := 2*netFact g * twinkle g k N
  have hp0 : 0 ≤ E := by
    have hg : 0<netFact g := netFact_pos
    have he : 0≤twinkle g k N := add_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (by norm_num) (bp_pos _).le)) (bp_pos _).le
    exact mul_nonneg (by positivity) he
  have hi (x : Bool→I→Knobs p.g n) (hx : w x≠0) :
      avg μ (fun o => F o (x true)*F o (x false)) ≤ E+ind (¬bloom p x) := by
    by_cases ht : bloom p x
    · have ha (i : Bool) : avg μ (fun o=> F o (x i))=0 := by
        let M := incision p l s f (x i)
        have he' := drill_law p (bloom_incision p n x l s f ht i) m h
        rw [sketch_matrix p l s f m a hj _ (draw_elem x i hx)] at he'
        change avg μ (fun o=>U (drill p M o))=0
        rw [←mapW_avg]; exact (congrArg (fun w=>avg w U) he').trans he
      let D i:=drQuery (p:=p) (A (x i))
      let W i:=U (relay (Comp p.g) I N i)
      have hg := bloom_drill p n x l s f ht
      have hz := pooled_batch D D m h k (fun i=>(port_limit g i).trans hk) hK hg hg
        (fun i=>W) (fun i y=>hh _)
      simp_rw [Fintype.prod_bool] at hz
      have heq (i : Bool) :
         avg μ (fun o=> W (peekR p (drStage p I) (D i) (D i) o))=0 := by
        specialize ha i
        unfold F at ha; simp_rw [drill_view p] at ha; exact ha
      change |_ - (avg μ _ * avg μ _)|≤_ at hz
      rw [heq true,heq false,mul_zero,sub_zero] at hz
      unfold F
      simp_rw [drill_view p]
      rw [ind_zero (fun hg=>hg ht),add_zero]
      exact (le_abs_self _).trans hz
    rw [ind_one ht]
    refine (hμ.avg_le (b:=1) ?_).trans (le_add_of_nonneg_left hp0)
    intro i
    have ht (a b : ℝ) (ha : |a| ≤ 1) (hb : |b|≤1) :
        a*b ≤1 := (le_abs_self _).trans (by rw [abs_mul]; exact
      (mul_le_mul ha hb (abs_nonneg _) zero_le_one).trans_eq (by ring))
    exact ht _ _ (hh _) (hh _)
  simp_rw [heq,avg_cross_sq]; rw [avg_avg]
  have ht :
      avg w (fun i=> E+ind (¬bloom p i))=E+pr w (fun i=>¬bloom p i) := by rw [avg_add,hW.avg_const];
                                                                            rfl
  apply le_trans _ (add_le_add_right (buds p n (fun i=>rung p n (a i))
    (fun i=>ticketFlow n _ hn)) E)
  change _ ≤ E + pr w (fun i=>¬bloom p i)
  rw [←ht]; unfold avg
  refine Finset.sum_le_sum (fun i _=> ?_)
  by_cases hi' : w i=0
  · change w i*_ ≤ w i*_
    simp only [hi',zero_mul,le_refl]
  exact mul_le_mul_of_nonneg_left (hi i hi') (hW.nz _)
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

end ExpSmall

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

theorem named_true {A : Type} {C : ℝ} (h : 1 ≤ C) :
    named (fun _ : A×A => True) C :=
  ⟨1,(by simpa using h),fun _ _ => True,fun _ => ⟨0,fun _ => Iff.rfl⟩⟩

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

end LeafMixture
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SyntheticTolerances
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Synthetic Tolerances -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Function Filter Real
open scoped BigOperators Topology
variable {p : Shape} {I : Type} [Fintype I] [DecidableEq I] {n N : ℕ}

theorem magazine_calendar (p : Shape) (I : Type) [Fintype I] [DecidableEq I]
    (M : ℕ) (hM : 1≤M) (hj : 1≤p.j) (L ε : ℝ) (hL : 0≤L) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, let N:=M*n; ∀ l s f, ∀ m : Mixer p n,2*num (Full p n)<N →
      ∀ P : Display p I N→Prop, ∀ a : I→Tickets p, ∀ w : Wgt (Orient p n N),
      IsLaw w → (∀ i,w i≤L*raw m N i) →
      (∀ i,w i≠0 → magazine p l s f P a i ≤ ε/2) →
      pr (displayLaw p I N (labGram p l f a)) P ≤ ε := by
  classical
  let g:= tied (drStage p I) Bool
  let k:=num I+num (Bool × Comp p.g × I)
  let C n := 2*netFact g*twinkle g k (M*n) + bp (num Bool*num I-(n:ℕ))
  have ht : Tendsto (fun n=>L*C n) atTop (𝓝 0) := by
    have hh {N:ℕ→ℝ} (h : Tendsto N atTop atTop) (i : ℝ) (b : ℝ) (hb : 0<b) :
        Tendsto (fun n => bp (i-b*N n)) atTop (𝓝 0) := by
      simp_rw [sub_eq_add_neg,bp_add,←neg_mul]
      simpa using ((bp_tendsto_zero hb).comp h).const_mul (bp i)
    have hN := cast_tops M hM
    have h1 := (hh hN k 1 (by norm_num))
    have h2 : Tendsto (fun n:ℕ => bp (-(↑(M*n):ℝ)/2)) atTop (𝓝 0) := by
      refine (tendsto_congr' ?_).mp (hh hN 0 (1/2) (by norm_num))
      exact .of_forall (fun x => by ring_nf)
    have h3 := hh (tendsto_natCast_atTop_atTop (R:=ℝ)) (num Bool*num I) 1 (by norm_num)
    have hv := (((((h1.const_mul 2).const_mul (num (Comp p.g))).add h2).const_mul
      (2*netFact g)).add h3).const_mul L
    simpa only [C,twinkle,mul_zero,zero_add,add_zero,one_mul] using hv
  let b:= ε/2
  have hb : 0<b := by positivity
  filter_upwards [ht.eventually (gt_mem_nhds (show 0<b^2 by positivity)),
    (cast_tops M hM).eventually (eventually_ge_atTop (2*k+1)),eventually_ge_atTop (2*p.r)]
    with n hn hq hU N l s f m hN P a w hw he h
  change 2*k+1 ≤ (N:ℝ) at hq
  have ha : num I ≤ k := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hk : num (Bool × Comp p.g × I)≤ k := le_add_of_nonneg_left (Nat.cast_nonneg _)
  let u := magazine p l s f P a (n:=n); let F:= pr (displayLaw p I N (labGram p l f a)) P
  let X i := (u i-F)^2
  have hh :
      avg (raw m N) X ≤ C n := magazine_var p l s f P a m hN hj hU (by linarith only [ha,hq])
        k hk (by linarith only [hq])
  by_contra! hl
  change ε<F at hl
  have hB : b^2 ≤ avg w X := by
    rw [← hw.avg_const (b^2)]; unfold avg
    apply Finset.sum_le_sum; intro i _
    by_cases he : w i=0
    · rw [he]; simp
    apply mul_le_mul_of_nonneg_left _ (hw.nz _)
    have hp : u i ≤ b := h i he
    change b^2≤ (u i-F)^2
    unfold b at *
    nlinarith only [hp,hε,hl]
  have hX : avg w X ≤ L*C n := by
    refine (avg_mono_left (fun i=>sq_nonneg (u i - F)) he).trans ?_
    apply le_trans ?_ (mul_le_mul_of_nonneg_left hh hL)
    simp only [X,avg,mul_assoc,Finset.mul_sum]
    exact le_rfl
  exact not_lt_of_ge (hB.trans hX) hn
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SyntheticParity
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Synthetic Parity -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Submodule Function Finset
open scoped BigOperators
variable {p : Shape} {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {d e n N : ℕ}

omit [DecidableEq I] in
theorem quad_cross_gen (Q : Mat I I) (x y z : Vec I) :
    evmat Q (z+x+y) (z+x+y)+evmat Q x x+(evmat Q y y+evmat Q z z)=
      evmat (Q+Qᵀ) (z+x) (z+y) := by
  rw [evmat_addM,evmat_transpose]
  unfold evmat; simp only [mulVec_add,add_dotProduct,dotProduct_add]
  ring_nf
  simp only [mul_two,char_two,zero_add,add_zero]

theorem arches_from (F : Vec (Hue d) → F) (Q : Mat (Hue d) (Hue d))
    (h : ∀ x,weightsAff x → F x=evmat Q x x) :
    arches F = pullM (plumeDiff d true) (plumeDiff d false) (Q+Qᵀ) := by
  classical
  ext i j
  let x:=jet (incarn i true); let y:=jet (incarn j false)
  let z:=jet (none : Hue d)
  have hj (x : Hue d) : weightsAff (jet x) := by simp [weightsAff,jet]
  have hz : weightsAff (z+x+y) := by
    unfold weightsAff
    simp only [Finset.sum_add_distrib,Pi.add_apply]
    rw [show ∑ i,z i=1 from hj _,show ∑ i,x i=1 from hj _,show ∑ i,y i=1 from hj _,char_two,zero_add]
  change F (z+x+y)+F x+(F y+F z)=_
  rw [h _ hz,h _ (hj _),h _ (hj _),h _ (hj _),quad_cross_gen]
  rw [pullM_def,Matrix.mul_assoc]
  rfl

theorem arches_rank (F : Vec (Hue d) → F) (Q : Mat (Hue d) (Hue d))
    (h : ∀ x,weightsAff x → F x=evmat Q x x) :
    (arches F).rank≤2*Q.rank := by
  rw [arches_from F Q h]
  refine le_trans (rank_lift_le ..) ?_
  rw [two_mul]
  exact (mrk_add_le ..).trans (by rw [Matrix.rank_transpose])

theorem arches_beam (d : ℕ) :
    arches (fun x => evmat (beamMap d) x x)= (1:Mat (Fin d) (Fin d)) := by
  classical
  ext i j
  have he (a b : Hue d) :
      evmat (beamMap d) (jet a) (jet b)=beamMap d a b := by simp [evmat,jet]

  let x:=jet (incarn i true); let y:=jet (incarn j false); let z:=jet (none:Hue d)
  change evmat _ (z+x+y) (z+x+y)+_+_=_
  rw [quad_cross_gen,evmat_addM,evmat_transpose]
  have h1 (a b c e : Hue d) : evmat (beamMap d) (jet a+jet b) (jet c+jet e)=
      beamMap d a c+beamMap d b c+(beamMap d a e+beamMap d b e) := by
    simp_rw [← he]; unfold evmat; rw [Matrix.mulVec_add,dotProduct_add,add_dotProduct,add_dotProduct]
  rw [h1,h1]
  simp [beamMap,Matrix.one_apply]

omit [DecidableEq I] in
theorem lib_see (p : Shape) (l s f) (x : I →Knobs p.g n)
    (u : Vec I) (h : weightsAff u) (o : Orient p n N) :
    let A := incision p l s f x
    let y := compound p x u
    libColor p l u (drill p A o) = keyOne p l s (lit f l y) o := by
  intro A y; funext i b
  cases b
  · change (primary _* A) *ᵥ u=primary _*ᵥ spring _ _ _ _ _
    rw [←Matrix.mulVec_mulVec,inc_compound p l s f x u h]; rfl
  change (primary _ * A)*ᵥ u=primary _*ᵥ spring _ _ _ _ _
  rw [← Matrix.mulVec_mulVec,inc_compound p l s f x u h]; rfl
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SyntheticArraySlices
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Synthetic Array Slices -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module Function LinearMap
open scoped BigOperators
variable {p : Shape} {d e n N : ℕ}
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem exhibit_law (p : Shape) (A : Mat I J) (G : Mat I I)
    (h : Injective A.mulVec) (hn : 2*num I-(N:ℝ) ≤ -1) :
    mapW (displayLaw p I N G) (exhibit p A)=displayLaw p J N (pullM A A G) := by
  classical
  let C := fun x:Mat I I=> x=G
  have he : gramGood (U:=Fin N) G = FramesAt C := rfl
  have hl : 2*num I<num (Fin N) := by simp only [num,Fintype.card_fin] at *; linarith only [hn]
  have hh : ∃ x : Rack I N,FramesAt C x := framesAt_exists (show ∃ x, C x from ⟨_,rfl⟩)
    (by rw [←two_mul]; exact hl)
  have hv :
      mapW (unifOn (gramGood (U:=Fin N) G)) (observe A A) = unifOn (gramGood (pullM A A G)) :=
    framesAt_observe hh _ _ h h (fun i (hi : i=G)=>hi ▸ rfl)
  have ht:=mapW_repeat (fun _ : Comp p.g=> unifOn (gramGood G)) (fun _ => observe (U:=Fin N) A A)
  rw [hv] at ht; exact ht

omit [DecidableEq I] [DecidableEq J] in
theorem exhibit_color (p : Shape) (A : Mat I J) (u : Vec J) (x : Display p I N) (l : Tag p.g) :
    libColor p l u (exhibit p A x)=libColor p l (A *ᵥ u) x := by
  funext i j; cases j
  · exact (Matrix.mulVec_mulVec ..).symm
  exact (Matrix.mulVec_mulVec ..).symm

theorem cart_target (f : Sextant d e) :
    pullM (cartM f) (cartM f) (beamMap e) =
      (beamMap e).submatrix (reflectSextant f) (reflectSextant f) := by
  rw [cartM,pullM_def,embedMat_mul,mul_embedMat]; rfl

theorem cart_cross (p : Shape) (f : Sextant d e) (l : Tag p.g) (s : Augur p N)
    (x : Display p (Hue e) N) :
    let Z:= arches (libAug p l s (beamMap e) x)
    arches (libAug p l s (pullM (cartM f) (cartM f) (beamMap e)) (exhibit p (cartM f) x))
      = Z.submatrix f.1 f.2 := by
  classical
  intro Z
  let A:= cartM f
  have hu (i : Hue d) : A*ᵥjet i=jet (reflectSextant f i) := by
    funext j; simp only [jet,Matrix.mulVec_single_one,col_apply,A,cartM,embedMat,
      Matrix.of_apply]
    by_cases h : j= reflectSextant f i <;> simp [h]
  have hx (u : Vec (Hue d)) :
      libAug p l s (pullM A A (beamMap e)) (exhibit p A x) u =
      libAug p l s (beamMap e) x (A*ᵥu) := by unfold libAug libPredict; rw [evmat_pull,exhibit_color]
  ext i j
  change arches (libAug p l s (pullM A A (beamMap e)) (exhibit p A x)) i j=Z (f.1 i) (f.2 j)
  unfold arches Z; dsimp only
  simp_rw [hx,mulVec_add,hu]
  rfl

omit [Fintype I] [DecidableEq I] in
theorem col_flag {K : Type} [Fintype K] {M : Mat K I} {f : J → I}
    (h : Injective (M.submatrix _root_.id f).mulVec) : Injective f := by
  classical
  intro i j hi
  let X:=M.submatrix _root_.id f
  have he : jet i=jet j := h (by
    rw [jet,jet,mulVec_single_one,mulVec_single_one]
    funext k; simp only [col_apply,Matrix.submatrix_apply,hi])
  by_contra! hg
  have hf := congr_fun he i
  simp only [jet,Pi.single_eq_same,Pi.single_eq_of_ne hg] at hf
  exact one_ne_zero hf

set_option maxHeartbeats 600000 in
theorem rank_torpedo (M : Mat (Fin e) (Fin e)) (d : ℕ)
    (h : ∀ f : Sextant d e,(M.submatrix f.1 f.2).rank<d) :
    M.rank<d := by
  classical
  by_contra! hh
  obtain ⟨g,hg⟩ := basis_subcolumns M
  let a := g ∘ Fin.castLE hh
  let A := M.submatrix _root_.id a
  have ha :
      Injective A.mulVec := inject_column_slice (M.submatrix _root_.id g) hg (Fin.castLE_injective hh)
  have hk : Aᵀ.rank=d := (Matrix.rank_transpose _).trans
    ((mrk_inj.mp ha).trans (Fintype.card_fin _))
  obtain ⟨f,hf⟩ : ∃ f : Fin d→Fin e,Injective (Aᵀ.submatrix _root_.id f).mulVec := by
    have he := basis_subcolumns Aᵀ; rwa [hk] at he
  let B := M.submatrix f a
  have hz : B.rank=d := by
    rw [← Matrix.rank_transpose]
    exact (mrk_inj.mp hf).trans (Fintype.card_fin _)
  have h1 : Injective a := col_flag ha
  have h2 : Injective f := col_flag hf
  have hu := h ⟨⟨f,h2⟩,⟨a,h1⟩⟩
  exact (ne_of_lt hu) hz
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_NumericalGramPrescriptions
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Numerical Gram Prescriptions -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Function LinearMap Module
open scoped BigOperators Pointwise
variable {p : Shape} {n N d e : ℕ} {I : Type} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
set_option maxHeartbeats 800000 in
theorem punch_real (p : Shape) (l : Tag p.g) (f : Flavor p.g) (G : Mat I I)
    (h : G.rank ≤ spacePunch p l f) :
    ∃ a : I→ Tickets p,labGram p l f a=G := by
  classical
  let P:= Finset.univ.filter (usesPunch p l f)
  let q:=Fintype.equivFinOfCardEq (Fintype.card_coe P)
  obtain ⟨u,v,hg⟩:=mul_factor G P.card h
  let x (i:I) (j:Punch p) := if h:j∈P then u i (q ⟨j,h⟩) else 0
  let y (i:I) (j:Punch p) := if h:j∈P then v (q ⟨j,h⟩) i else 0
  let a (i:I) : Tickets p := fun j => if j.2 then x i j.1 else y i j.1
  refine ⟨a,?_⟩
  rw [←hg]; ext i j
  change (∑ t:Punch p,(if usesPunch p l f t then a i (t,true)*a j (t,false) else 0))=∑ t,u i t * v t j
  have ht (t:Punch p) : a i (t,true)*a j (t,false)=x i t*y j t := rfl
  simp_rw [ht,← Finset.sum_filter]
  change ∑ t∈P,x i t*y j t=_
  calc _ = ∑ t:P,x i t.val*y j t.val := Eq.symm (Finset.sum_coe_sort P (fun t=>x i t*y j t))
       _ = _ := by
        have hh (t : ↑P) : x i t.val*y j t.val=u i (q t)*v (q t) j := by
          unfold x y; rw [dite_eq_left t.property,dite_eq_left t.property]
        simp_rw [hh]; exact Equiv.sum_comp q (fun t=>u i t*v t j)

theorem beam_rank (f : Sextant d e) : (pullM (cartM f) (cartM f) (beamMap e)).rank≤d := by
  classical
  rw [cart_target]
  let V := (beamMap e).submatrix (reflectSextant f) (reflectSextant f)
  let P : Mat (Hue d) (Fin d) := embedMat (fun x=>incarn x true)
  let Q : Mat (Fin d) (Hue d) := Matrix.of fun i j => V (incarn i true) j
  have hnone (j : Hue d) : V none j = 0 := rfl
  have hfalse (i : Fin d) (j : Hue d) : V (some (false,i)) j = 0 := by
    cases j with
    | none => rfl
    | some j => rcases j with ⟨b,j⟩; cases b <;> rfl
  have h : P*Q=V := by
    ext i j
    rcases i with _|⟨b,i⟩
    · simp [Matrix.mul_apply,P,embedMat,incarn,hnone]
    cases b
    · simp [Matrix.mul_apply,P,embedMat,incarn,hfalse]
    · simp [Matrix.mul_apply,P,Q,embedMat,incarn]
  change V.rank≤ d
  rw [←h]
  exact (Matrix.rank_mul_le_left ..).trans ((P.rank_le_card_width).trans_eq (by simp))

theorem sharedPunch (p : Shape) (hr : 1≤p.r) (l : Tag p.g) :
    1 ≤ spacePunch p l Flavor.sharedOnly := by
  let i : Punch p := (.inr (),⟨0,hr⟩)
  exact Finset.card_pos.mpr ⟨i,Finset.mem_filter.mpr ⟨mem_univ _,trivial⟩⟩

theorem purePunch (p : Shape) (l : Tag p.g) (E : Finset (Tag p.g)) :
    ((p.g-1)/2)*(p.g-E.card)*p.r ≤ spacePunch p l (creed p E) := by
  classical
  let u := Finset.univ.filter (fun i=> allowed i l)
  let v := Finset.univ\ E
  let Z := u ×ˢ (v ×ˢ (Finset.univ : Finset (Fin p.r)))
  let f (i : Tag p.g × Tag p.g × Fin p.r) : Punch p := (.inl (i.1,i.2.1),i.2.2)
  have hf : Injective f := by
    rintro ⟨i,j,k⟩ ⟨x,y,z⟩ h
    simpa only [Prod.mk.injEq,Sum.inl.injEq,f,and_assoc] using h
  have he : Z.image f⊆ Finset.univ.filter (usesPunch p l (creed p E)) := by
    rintro i hi
    obtain ⟨⟨i,j,k⟩,hv,rfl⟩:=mem_image.mp hi
    simp only [Z,u,v,mem_product,mem_sdiff,mem_filter,mem_univ,true_and,and_true] at hv
    refine mem_filter.mpr ⟨mem_univ _,?_⟩
    exact ⟨hv.1,mem_filter.mpr ⟨mem_univ _,hv.2⟩⟩
  have ht := card_le_card he
  rw [card_image_of_injective _ hf] at ht
  have hu : u.card=(p.g-1)/2 := by
    have h:= card_allowed' l; rw [Fintype.card_subtype] at h; exact h
  unfold spacePunch
  refine le_trans ?_ ht
  unfold Z v; rw [card_product,card_product,Finset.card_sdiff_of_subset (subset_univ _),
    card_univ,card_univ,hu,Fintype.card_fin,Fintype.card_fin,
    mul_assoc]
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ZeroDiscrepancyPrediction
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Zero Discrepancy Prediction -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Submodule Function
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

theorem zoom_le (w : Tag p.g → Moment p n) : (zoomset p w).card≤ (nonzeroTags w).card := by
  apply Finset.card_le_card
  intro i hi
  exact (mem_nonzeroTags i w).mpr (fun he => (mem_filter.mp hi).2 (by rw [he,map_zero]))

set_option maxHeartbeats 600000 in
theorem coreRole (p : Shape) (w : Tag p.g→Moment p n) (hw : ∀ t,w t∈Wtag p n t)
    (α : F) (hg : Odd p.g) (h : parityW w+α=1) (l s x) :
    let f:= creed p (zoomset p w)
    let M:=useAtom p l s f x
    T0 p n (cut p n w) M + α*role p n M=dialed p l f x := by
  classical
  intro f M
  let U:=cut p n w
  let Q:= scan p l f x
  have h1 : Q (.inr ())=0 := by simp [Q,f,scan,creed,Flavor.keeps,asBlock,Block.S]
  have hq : role p n M=dialed p l f x := by
    rw [role_scan]
    change Q.diagO=Q.sumBit; unfold Digest.sumBit; rw [h1,add_zero]
  let E:=zoomset p w
  have hh t : sharedT p n t M=0 := by rw [sharedT_scan p hg]; change Q _+(if l=t then Q _ else 0)=_
                                           ; rw [h1]; simp
  have he t (ht : t∈ E) : roleT p n t M=0 := by
    rw [roleT_scan p]
    refine sum_eq_zero fun i _ => ?_
    have hv : ¬ f.keeps l (Block.O i t) := fun hx=> (mem_filter.mp hx.2).2 ht
    unfold scan; exact ite_eq_right hv
  have hl t (hE : t∉E) :
      role p n U+sharedT p n t U+α=1 := by
    have hz : etab p n Block.S (w t)=0 := not_ne_iff.mp (fun hg=>hE (mem_filter.mpr ⟨mem_univ _,hg⟩))
    unfold U
    rw [role_cut p w hw,sharedT_cut p hg t,hz,add_zero,← Finset.sum_add_distrib]
    exact h
  rw [T0_val]; change role _ _ U* _ + _ + _ = _
  simp_rw [hh,mul_zero,zero_add]
  rw [←hq]
  let r := role p n U
  have hm : role p n M=∑ t, roleT p n t M := by unfold role; rw [LinearMap.sum_apply]
  rw [hm,mul_sum,mul_sum,←sum_add_distrib,←sum_add_distrib]
  refine Finset.sum_congr rfl fun t _=>?_
  by_cases ht : t∈E
  · rw [he t ht]; ring
  rw [← add_mul,←add_mul,hl t ht,one_mul]

theorem inner_gem (p : Shape) (x : UnitType p n N) (i : Bool) (t : Tag p.g) :
    ∃ M : Moment p n,M.rank ≤ (p.g-1)*p.h ∧ ∀ (s z),
      innerP p x i (atom p t s z)=mpair M (mom p s z) := by
  classical
  let A:=onSide x i; let B:=onSide x (!i)
  let P (e : Comp p.g) := channel (B e).2*(channel (B e).1)ᵀ
  let Z (e : Comp p.g) := liftM (primary (A e).1)ᵀ (primary (A e).2)ᵀ (P e)
  let M := ∑ i:TagStar t,Z i.val
  have ht i : (Z i).rank ≤ p.h := (rank_lift_le ..).trans ((Matrix.rank_mul_le_left ..).trans
    ((Matrix.rank_le_card_width (channel (B i).2)).trans_eq (by simp)))
  refine ⟨M,(mrk_sum_le ..).trans ((Finset.sum_le_sum (fun i _=>ht i.val)).trans_eq ?_),?_⟩
  · simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,card_star]
  intro s z
  change (∑ i:Comp p.g, mpair (P i) (liftM (primary (A i).1) (primary (A i).2) (atom p t s z i)))
    =_
  let Q:= mom p s z
  have he i :
      mpair (P i) (liftM (primary (A i).1) (primary (A i).2) (atom p t s z i)) =
      if inc i t then mpair (Z i) Q else 0 := by
    rw [mpair_liftM,atom_def]; by_cases ht:inc i t <;> simp only [ht,ite_false, if_false,ite_true, if_true,map_zero]; rfl
  simp_rw [he]
  unfold M; rw [←Finset.sum_filter,mpair_sum]; exact Finset.sum_subtype _ (by simp) _

theorem zero_screen (p : Shape) (x : UnitType p n N) (i : Bool) (s : Label p.b)
    (m : Mixer p n) (α : F) (hg : Odd p.g)
    (w : Tag p.g→Moment p n) (hw : ∀ i,w i∈ Wtag p n i) (h : parityW w+α=1)
    (K : ℕ) (hk : totalRank (cut p n w) ≤ K) (g : Augur p N)
    (δ : ℝ) (L : Finset (Label p.b)) (hs : s∉ L)
    (hz : postulates p (onSide x i) g (yoke p m x i (cut p n w) α) L δ) :
    screen p (onSide x i) s (zoomset p w) (screenRank p K) g δ := by
  classical
  let a := cut p n w; let f:=creed p (zoomset p w)
  refine ⟨_,hz s hs,fun l=>?_⟩
  obtain ⟨M,hM,ht⟩:=inner_gem p x i l
  refine ⟨M+qmix m a l,le_trans (mrk_add_le ..) ?_,fun y=>?_⟩
  · refine (Nat.add_le_add hM (qmix_rank ..)).trans ?_
    unfold screenRank; change _+p.J*(p.g-1)*(2*totalRank a)≤_
    exact le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left (p.J*(p.g-1))
      (Nat.mul_le_mul_left 2 hk)) _) (le_of_eq (by ring))
  let A:=useAtom p l s f y
  let z:=lit f l y; let T:=mom p s z
  have h0 : (Tsym m a+α • role p n) A= dialed p l f y+mpair (qmix m a l) T := by
    have hh : Tmix m a A=mpair (qmix m a l) T := Tmix_atom ..
    change T0 p n a A + Tmix m a A + α * role p n A=_
    rw [hh,add_right_comm]
    exact congrArg (·+_) (coreRole p w hw α hg h l s y)
  change innerP p x i A + (Tsym m a + α • role p n) A = dialed p l f y+_
  rw [show innerP p x i A=mpair M T from ht s z,h0, ←mpair_outer,mpair_add]
  change mpair M T+(dialed p l f y + _) = dialed p l f y+(mpair M T+_)
  rw [add_left_comm]; rfl
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SyntheticFailureBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Synthetic Failure Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Function Filter Real
open scoped BigOperators
variable {p : Shape} {I A : Type} [Fintype I] [DecidableEq I] [Fintype A] {n N d : ℕ}

theorem pr_mono_support (w : Wgt A) (hw : ∀ i, 0≤w i) {P Q : A→Prop}
    (h : ∀ i, w i≠0→P i→Q i) :
    pr w P ≤ pr w Q := by
  change ∑ i,w i*ind (P i) ≤ ∑ i,w i*ind (Q i)
  refine Finset.sum_le_sum fun i _=> ?_
  by_cases hi : w i=0
  · rw [hi,zero_mul,zero_mul]
  exact mul_le_mul_of_nonneg_left (ind_mono (h i hi)) (hw i)

theorem fiddle_bound (p : Shape) (S : Knobs p.g n → Prop) (w : I→ Tickets p)
    (h : 2*p.r≤n) (ε : ℝ) (hS : pr (spins p n) S≤ ε) :
    pr (sketchLaw p n w) (fun i=> ∃ x,weightsAff x ∧ S (compound p i x))
      ≤ fiddleRate p I * ε := by
  classical
  let P (x : Vec I) := fun i : I → Knobs p.g n=> weightsAff x ∧ S (compound p i x)
  have hw := sketch_law p n w h
  have hi (i:Vec I) :
      pr (sketchLaw p n w) (P i) ≤ (labFee p I)⁻¹*ε := by
    have hg : 0 < labFee p I := labFee_pos ..
    by_cases he : weightsAff i
    · unfold P; simp only [he,true_and]; exact
        (sketch_point p n w h i he S).trans (mul_le_mul_of_nonneg_left hS (by positivity))
    have he' := (pr_nonneg (spins_law p n).nz).trans hS
    simp only [P,he,false_and,pr_false] <;> positivity
  exact (pr_exists_le hw.nz P).trans ((Finset.sum_le_sum (fun i _ => hi i)).trans_eq
    (by simp only [fiddleRate,num,Finset.sum_const,card_univ,nsmul_eq_mul,mul_assoc]))

set_option maxHeartbeats 800000 in
theorem havoc_rate (p : Shape) (l : Tag p.g) (o : Orient p n N) (g : Augur p N) (E : Finset (Tag p.g))
    (s : Label p.b) (r : ℕ) (m : Mixer p n) (ε : ℝ)
    (a : Hue d → Tickets p) (hj : 1≤p.j) (hn : 2*p.r≤n)
    (hx : screen p o s E r g ε) :
    let f:= creed p E
    magazine p l s f (havoc p l g (labGram p l f a) r) a o ≤ fiddleRate p (Hue d)*ε := by
  classical
  intro f
  let G:= labGram p l f a
  obtain ⟨w,h1,h2⟩:=hx
  obtain ⟨M,hM,h⟩:=h2 l
  let P:= mismatch p g w l s f o
  let v:=sketchLaw p n a
  apply le_trans _ (fiddle_bound p P a hn ε (h1 l f))
  change pr v _≤ pr v _
  refine pr_mono_support v (sketch_law p n a hn).nz fun x hx hh=>?_
  by_contra! he
  let A:= incision p l s f x
  let T:=pullM A A M; let F:=libAug p l g G (drill p A o)
  have hi : pullM A A (selfM p n m.mixM) = G := sketch_matrix p l s f m a hj x hx
  have hz (y : Vec (Hue d)) (hy : weightsAff y) :
      F y=evmat T y y := by
    let t:=compound p x y
    have ht : ¬ P t := he y hy
    have heq : g l (evmat G y y) (libColor p l y (drill p A o))=
        dialed p l f t+evmat T y y := by
      rw [←hi,inc_diag _ l s f m x y hy hj,lib_see p l s f x y hy o]
      have he := Eq.symm (not_ne_iff.mp ht)
      refine he.trans ((h t).trans ?_)
      unfold T; rw [evmat_pull,inc_compound p l s f x y hy]
    unfold F libAug libPredict
    rw [heq,←hi,inc_diag _ l s f m x y hy hj]
    change dialed p l f t+_ + dialed p l f t=_
    rw [add_right_comm,char_two,zero_add]
  have hl := (arches_rank F T hz).trans (Nat.mul_le_mul_left 2 ((rank_lift_le ..).trans hM))
  exact Nat.not_lt_of_ge hl hh

theorem common_lit (p : Shape) (j l : Tag p.g) (x : Knobs p.g n) :
    lit Flavor.sharedOnly j x=lit Flavor.sharedOnly l x := by
  classical
  funext i
  rcases i with ⟨x|x,i⟩
  · simp [lit,Flavor.keeps]
  simp [lit,Flavor.keeps]
theorem common_dial (p : Shape) (j l : Tag p.g) (x : Knobs p.g n) :
    dialed p j Flavor.sharedOnly x=dialed p l Flavor.sharedOnly x := by
  have hj := etaScan p j (0:Label p.b) Flavor.sharedOnly x
  have hl := etaScan p l (0:Label p.b) Flavor.sharedOnly x
  rw [common_lit p j l x] at hj; exact hj.trans hl.symm

set_option maxHeartbeats 800000 in
theorem mute_rate (p : Shape) (l : Tag p.g) (o : Orient p n N) (g : Augur p N) (E : Finset (Tag p.g))
    (s : Label p.b) (r : ℕ) (m : Mixer p n) (ε : ℝ)
    (a : Unit→ Tickets p) (hj : 1≤p.j) (hn : 2*p.r≤n)
    (hx : screen p o s E r g ε) :
    let f:= Flavor.sharedOnly
    magazine p l s f (mute p g (labGram p l f a)) a o ≤ p.g*fiddleRate p Unit*ε := by
  classical
  intro f; let G:=labGram p l f a
  obtain ⟨w,h1,h2⟩:=hx
  let P (i:Tag p.g):= mismatch p g w i s f o
  let Q := fun x=>∃ i,P i x
  let W:=sketchLaw p n a
  have he : pr (spins p n) Q≤p.g*ε := by
    refine (pr_exists_le (spins_law p n).nz P).trans ((sum_le_sum
      (fun i _=> h1 i f)).trans_eq ?_)
    simp only [Finset.sum_const,nsmul_eq_mul,card_univ,Tag,Fintype.card_fin]
  apply le_trans _ ((fiddle_bound p Q a hn (p.g*ε) he).trans_eq (by ring))
  change pr W _ ≤ pr W _
  refine pr_mono_support W (sketch_law p n a hn).nz fun x hx hh=>?_
  by_contra! H
  let A:= incision p l s f x
  let u:= jet ()
  have hu : weightsAff u := by simp [weightsAff,u,jet]
  let t:= compound p x u
  have ht : ∀ i,¬ P i t := not_exists.mp (H u hu)
  have hZ : pullM A A (selfM p n m.mixM) = G := sketch_matrix p l s f m a hj x hx
  have heq i :
      libPredict p i g G (drill p A o) u = w (atom p i s (lit f l t)) := by
    have hq : evmat G u u=dialed p i f t := by rw [←hZ,inc_diag _ l s f m x u hu hj];
                                                exact common_dial p l i t
    have hg : A=incision p i s f x := by
      ext y j; unfold A incision
      simp only [Matrix.of_apply,spring, f]
      rw [common_lit p l i]
    unfold libPredict; rw [hq,hg,lib_see p i s f x u hu o]
    rw [show lit f l t=lit f i t from common_lit p l i t]
    exact Eq.symm (not_ne_iff.mp (ht i))
  apply hh; change ∑ i:Tag p.g,libPredict p i g G (drill p A o) u=_
  simp_rw [heq,←map_sum,atom_union,map_zero]
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_OppositePredictions
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Opposite Predictions -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Function Filter Real
open scoped BigOperators
variable {p : Shape} {e d n N : ℕ}

theorem single_jet {I : Type} [Fintype I] (x : Vec I) :
    singleEx x *ᵥ jet ()=x := by funext j; simp [singleEx,jet,Matrix.mulVec,dotProduct]
theorem single_ind {I : Type} [Fintype I] (x : Vec I) (h : weightsAff x) :
    Injective (singleEx x).mulVec := by
  classical
  obtain ⟨j,hj⟩ : ∃ j,x j≠0 := by
    by_contra! hz
    unfold weightsAff at h
    simp only [hz,Finset.sum_const_zero] at h; exact zero_ne_one h
  intro a b ha; funext k
  have hh := congr_fun ha j
  unfold singleEx Matrix.mulVec dotProduct at hh; simp at hh
  cases k; exact hh.resolve_right hj

private theorem collision_front (p : Shape) {r e : ℕ} (h : p.g*(2*r)<e)
    (hg : Odd p.g)
    (x : Display p (Hue e) N) (g : Augur p N)
    (hh : ∀ i,weightsAff i→∑ l:Tag p.g,libPredict p l g (beamMap e) x i=0)
    (hA : ∀ j:Sextant (2*r+1) e,∀ l,¬ havoc p l g (pullM (cartM j) (cartM j) (beamMap e))
      r (exhibit p (cartM j) x)) : False := by
  classical
  let Q (i : Vec (Hue e)) := evmat (beamMap e) i i
  let A (l : Tag p.g) := libAug p l g (beamMap e) x
  let B (i : Vec (Hue e)) := ∑ l : Tag p.g,A l i
  have he i (hi : weightsAff i) :
      B i=evmat (beamMap e) i i := by
    unfold B A libAug; rw [Finset.sum_add_distrib,hh i hi]
    simp only [Finset.sum_const,Finset.card_univ,Tag,Fintype.card_fin,odd_smul_bit hg,zero_add]
  have hz : ∑ l : Tag p.g, arches (A l)=arches B := by
    ext i j; rw [Matrix.sum_apply]; unfold arches
    simp only [Matrix.of_apply,B, ← Finset.sum_add_distrib]
  rw [arches_from B (beamMap e) he] at hz
  have hQ := arches_from Q (beamMap e) (fun x _=>rfl)
  have hi : arches Q=1 := arches_beam _
  rw [← hQ,hi] at hz
  have h1 l : (arches (A l)).rank ≤ 2*r := by
    apply Nat.le_of_lt_succ
    apply rank_torpedo
    intro f
    have hv := hA f l
    unfold havoc at hv
    rw [cart_cross p f l g x] at hv
    exact Nat.lt_succ_of_le (le_of_not_gt hv)
  have ht := mrk_sum_le univ (fun l:Tag p.g=> arches (A l))
  rw [hz,Matrix.rank_one,Fintype.card_fin] at ht
  have he' := ht.trans (Finset.sum_le_sum (g:=fun _=>2*r) (fun i _=>h1 i))
  simp only [Finset.sum_const,Finset.card_univ,Tag,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at he'
  exact not_lt_of_ge he' h

set_option maxHeartbeats 1600000 in
theorem screen_calendar (p : Shape) (r M : ℕ) (hM : 1 ≤ M) (L : ℝ) (hL : 0≤ L)
    (hr : 1≤p.r) (hj : 1≤p.j) (hg : Odd p.g) :
    ∃ ε : ℝ,0<ε ∧ ∀ᶠ n : ℕ in atTop, let N:= M*n; ∀ m : Mixer p n,2*num (Full p n)<N →
      ∀ (E : Finset (Tag p.g)), 2*r+1≤ ((p.g-1)/2)*(p.g-E.card)*p.r →
      ∀ (s : Label p.b) (g : Augur p N) (w : Wgt (Orient p n N)), IsLaw w →
      (∀ i,w i≤ L*raw m N i) → (∀ i,w i≠0 → screen p i s E r g ε) → False := by
  classical
  let e:=p.g*(2*r)+1
  let d:=2*r+1
  let B:=Vec (Hue e)
  let A:= B ⊕ (Sextant d e ×Tag p.g)
  have ha : 0<num A := by unfold num; positivity
  let u := 1/num A/2
  have hu : 0 < u := by positivity
  let b:= (p.g:ℝ)*fiddleRate p Unit
  let c:= fiddleRate p (Hue d)
  have hf (d : ℕ) : 0 ≤ fiddleRate p (Hue d) := mul_nonneg (Nat.cast_nonneg _)
    ((inv_pos_of_pos (labFee_pos ..)).le)
  have hc : 0 ≤ c := hf d
  have hb : 0≤b := mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _)
    ((inv_pos_of_pos (labFee_pos ..)).le))
  let t:=b+c+1
  have ht : 0<t := by unfold t; linarith
  let ε:=u/2/t
  have hε : 0<ε := by positivity
  have hh : c*ε ≤ u/2 ∧ b*ε≤u/2 := by
    have he : t*ε=u/2 := by unfold ε; field_simp
    unfold t at he
    constructor <;> nlinarith only [he,hε,hb,hc]
  refine ⟨ε,hε,?_⟩
  filter_upwards [magazine_calendar p Unit M hM hj L u hL hu,
    magazine_calendar p (Hue d) M hM hj L u hL hu,
    (cast_tops M hM).eventually (eventually_ge_atTop (2*num (Hue e)+1)),
    eventually_ge_atTop (2*p.r)] with n hn hF hB hU N m hN E hE s g w hw h h'
  let W:= Display p (Hue e) N; let Q:= displayLaw p (Hue e) N (beamMap e)
  change 2*num (Hue e)+1≤ (N:ℝ) at hB
  have hB : 2*num (Hue e)-(N:ℝ) ≤ -1 := by linarith only [hB]
  have hQ : IsLaw Q := display_law p (beamMap e) N hB
  let f:= Flavor.sharedOnly (g:=p.g); let z:=creed p E
  let P (i:A) (x:W) :=
    match i with
    | .inl i => weightsAff i ∧ ∑ j:Tag p.g,libPredict p j g (beamMap e) x i≠0
    | .inr (j,i) => havoc p i g (pullM (cartM j) (cartM j) (beamMap e)) r (exhibit p (cartM j) x)
  have he (i:A) : pr Q (P i) ≤ u := by
    rcases i with i|⟨i,j⟩
    · by_cases hi : weightsAff i
      · let V:=singleEx i; let G:=pullM V V (beamMap e)
        let R:=mute p g G
        have hv :
            P (.inl i)= (fun x=>R (exhibit p V x)) := by
          unfold P
          simp only [hi,true_and,R,mute,libPredict,G,evmat_pull,exhibit_color,
            V,single_jet]; rfl
        have hG : 0<p.g := by obtain ⟨_,hh⟩:=hg; omega
        let j:Tag p.g := ⟨0,hG⟩
        obtain ⟨a,ha⟩ := punch_real p j f G (G.rank_le_card_width.trans
          ((by simp : Fintype.card Unit ≤1).trans (sharedPunch p hr j)))
        rw [hv,←mapW_pr]
        unfold Q; rw [exhibit_law p _ _ (single_ind _ hi) hB, show pullM _ _ _ = _ from ha.symm]
        apply hn j s f m hN R a w hw h
        intro x hx
        have hz := mute_rate p j x g E s r m ε a hj hU (h' x hx)
        unfold R; rw [←ha]; exact hz.trans hh.2
      have ht : P (Sum.inl i)=(fun _=>False) := by funext; simp [P,hi]
      rw [ht]; exact (pr_false Q).le.trans hu.le
    let V:= cartM i; let G:=pullM V V (beamMap e)
    let R:= havoc p j g G r
    have hv :
        P (Sum.inr (i,j))=(fun x=>R (exhibit p V x)) := rfl
    have he : Injective V.mulVec := embedMat_inj (reflectSextant i).injective
    have h1 : d ≤ spacePunch p j z := hE.trans (purePunch p j E)
    obtain ⟨a,ha⟩ := punch_real p j z G ((beam_rank i).trans h1)
    rw [hv,←mapW_pr]
    unfold Q; rw [exhibit_law p _ _ he hB,show pullM _ _ _=_ from ha.symm]
    apply hF j s z m hN R a w hw h
    intro x hx
    have hz := havoc_rate p j x g E s r m ε a hj hU (h' x hx)
    unfold R; rw [←ha]; exact hz.trans hh.1
  have hh x : ∃ i,P i x := by
    by_contra! hh
    refine collision_front p (r:=r) (Nat.lt_succ_self _) hg x g ?_ ?_
    · intro i hi
      exact not_ne_iff.mp fun h=> hh (.inl i) ⟨hi,h⟩
    exact fun i j=>hh (Sum.inr (i,j))
  have hi := pr_exists_le hQ.nz P
  have he' := hi.trans ((Finset.sum_le_sum (fun i _=>he i)).trans_eq (by
    rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]))
  change pr Q _≤ num A*u at he'
  rw [show (fun x=>∃ i,P i x)=(fun x=>True) from funext (fun i=>propext ⟨fun _=> trivial,fun _=>hh i⟩),
    pr_true,hQ.total,show num A*u=(1/2:ℝ) by unfold u; field_simp] at he'
  linarith only [he']
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PhaseClassCompatibility
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype
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

open PredictionClass

theorem zero_delta (z : BMark p n N) (x : UnitType p n N) (h : delta z x=0) :
    Uembed x.1 (z x true)=Uembed x.2 (z x false) := by
  exact add_right_cancel (h.trans (char_two _).symm)

theorem exactInner (m : Mixer p n) (z : BMark p n N) (x : UnitType p n N)
    (h : exactInk p m z x) :
    ∀ i, ∀ v∈Xspace p n,innerP p x i v = grad m (z x i) v := by
  intro i v hv
  have he := h i v hv
  change innerP p x i v+(Tsym m (z x i) v +1*role p n v)=0 at he
  rw [one_mul,add_comm (Tsym m (z x i) v),← grad_val] at he
  exact add_right_cancel (he.trans (char_two _).symm)

theorem delta_dusk (m : Mixer p n) (z : BMark p n N) (x : UnitType p n N)
    (hx : ∀ i,z x i∈Xspace p n)
    (h : exactInk p m z x) (hz : delta z x=0)
    (he : (rawHoles m).unit x) (hi : ∀ i,frameLaw m (onSide x i)) :
    glint p (z x)=0 := by
  apply (bit_cases _).resolve_right
  intro hh
  have heq := exactInner m z x h
  unfold glint at hh; rw [Fintype.sum_bool] at hh
  apply he
  exact ⟨hi true,hi false,z x true,z x false,hx _,hx _,zero_delta z x hz,heq true,heq false,hh⟩

theorem fade (c : PredictionClass) (α : Party) (r : F)
    (h : c.lit α) (hα : α true=α false) (hd : c=dusk → r=0)
    (Δ : UnitType p n N→Ambient p N) (x : UnitType p n N × UnitType p n N)
    (hx : Δ x.1=0) (hy : Δ x.2=0) :
    c.matchUp Δ α r x := by
  classical
  have ht : quench p Δ x=0 := by
    unfold quench tone; rw [hx,hy]
    simp only [map_zero]; rfl
  unfold matchUp; rw [ht]
  cases c
  · rw [hd rfl]; rfl
  · rename_i i
    cases i
    · have hh : firstBit α true=0 := h.1 true (show false≠true from Bool.false_ne_true)
      unfold firstBit at hh; rw [hα] at hh
      exact (zero_add _).trans hh.symm
    have hh : firstBit α false=0 := h.1 false (show true≠false from Ne.symm Bool.false_ne_true)
    unfold firstBit at hh; rw [←hα] at hh
    exact (zero_add _).trans hh.symm
  · simp [compatible]
  trivial

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ZeroDiscrepancyLemma
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Zero Discrepancy Lemma -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Finset Function Filter Real
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {A B : Type} [Fintype A] [Fintype B]

theorem weighted_some [Nonempty B] {w : Wgt A} (h : IsLaw w) (f : B → A→Prop)
    (he : ∀ i,w i≠0 → ∃ j,f j i) :
    ∃ j,(num B)⁻¹ ≤ pr w (f j) := by
  classical
  have hi : pr w (fun _=> True) ≤ pr w (fun i=>∃ j,f j i) := pr_mono_support w h.nz
    (fun i hi _=> he i hi)
  have hx := hi.trans (pr_exists_le h.nz f)
  rw [pr_true,h.total] at hx
  by_contra! hh
  have ht : ∑ i:B,pr w (f i)<∑ i:B,(num B)⁻¹ := by
    obtain ⟨i⟩ := (inferInstance:Nonempty B)
    exact Finset.sum_lt_sum (fun i _=> (hh i).le) ⟨i,mem_univ _,hh i⟩
  have hb : (num B:ℝ)≠0 := by unfold num; positivity
  simp only [sum_const, card_univ,nsmul_eq_mul] at ht
  change ∑ i:B,pr w _<num B*(num B)⁻¹ at ht
  rw [mul_inv_cancel₀ hb] at ht; exact not_lt_of_ge hx ht

set_option maxHeartbeats 1200000 in
theorem unit_screen (p : Shape)
    (K D q B : ℕ)
    (hD : 4*D≤ p.g*q) (hg : 8*D<p.g*p.g)
    (hB : B < Fintype.card (Label p.b))
    (m : Mixer p n) (x : UnitType p n N)
    (hg' : Odd p.g) (hj : 1≤p.j)
    (v : Bool → Profile p n) (α : Bool → F) (ha : α true≠α false)
    (hy : ∀ i, v i ∈ Xspace p n ∧ totalRank (v i) ≤ K ∧ frameLaw m (onSide x i))
    (hz : joins x ≤2*D) (h : Uembed x.1 (v true)=Uembed x.2 (v false))
    (L : Bool→ Finset (Label p.b)) (hL : ∀ i,(L i).card≤B)
    (g : Bool→Augur p N) (ε : ℝ)
    (he : claimed p x g m v α L ε) :
    ∃ (s : Label p.b) (E : Finset (Tag p.g)), E.card≤ q ∧ ∃ b,
      screen p (onSide x b) s E (screenRank p K) (g b) ε := by
  classical
  have hxA : frameLaw m x.1 := (hy true).2.2
  have hxB : frameLaw m x.2 := (hy false).2.2
  obtain ⟨h1,h2⟩:=totalRank_shared hxA hxB h
  have ht (i:Bool) : totalRank (v i) ≤2*D := by
    cases i
    · rw [←h1]; exact h2.trans hz
    exact h2.trans hz
  choose w hw hW hs ht' using fun i:Bool=> sparse_rep (hy i).1
    (show 4*totalRank (v i)<p.g*p.g by have hM:=ht i; omega)
  have hP : parityW (w true)=parityW (w false) :=
    parityW_shared hj hxA hxB (hW _) (hW _) (by rw [hw,hw,h]) (ht' _) (ht' _)
  obtain ⟨b,hb⟩ : ∃ b, parityW (w b)+α b=1 := by
    by_contra! hv
    have hz (i:Bool) : parityW (w i)+α i=0 := (bit_cases _).resolve_right (hv i)
    have hx := hz true; rw [hP] at hx
    exact ha (add_left_cancel (hx.trans (hz false).symm))
  obtain ⟨s,hf⟩ : ∃ s,s∉L b := by
    by_contra! h
    have hz : univ ⊆ L b := fun i _=>h i
    have hh := (card_le_card hz).trans (hL b); rw [card_univ] at hh; omega
  have hx : 0<p.g := by obtain ⟨_,hh⟩:=hg'; omega
  refine ⟨s,zoomset p (w b), le_trans (zoom_le _) ?_,b,?_⟩
  · apply Nat.le_of_mul_le_mul_left _ hx
    have hm:=hs b; have hv:=ht b; omega
  exact zero_screen p x b s m (α b) hg' _ (hW b) hb K (by rw [hw]; exact (hy b).2.1)
    _ ε (L b) hf (by rw [hw]; exact he b)

set_option maxHeartbeats 1200000 in
theorem silicon_calendar (p : Shape)
    (M K D q B : ℕ) (hM : 1 ≤ M)
    (hD : 4*D≤ p.g*q) (hg : 8*D<p.g*p.g)
    (hB : B < Fintype.card (Label p.b))
    (hj : 1≤p.j) (hg' : Odd p.g) (hr : 1≤p.r)
    (hs : 2*screenRank p K+1 ≤ ((p.g-1)/2)*(p.g-q)*p.r)
    (L : ℝ) (hL : 0≤L) :
    ∃ ε:ℝ,0<ε∧∀ᶠ n : ℕ in atTop,
      let N:=M*n; let U:=UnitType p n N
      ∀ m : Mixer p n, 2*num (Full p n)<N →
      ∀ (w : Wgt U) (α : Bool→F) (g : Bool→Augur p N), IsLaw w → bySide p w m L →
      (∀ x,w x≠0 → joins x≤2*D ∧ ∃ (v : Bool → Profile p n) (H : Bool → Finset (Label p.b)),
        (∀ i:Bool,(H i).card≤B ∧ v i∈ Xspace p n ∧ totalRank (v i) ≤ K ∧ frameLaw m (onSide x i))
          ∧ Uembed x.1 (v true)=Uembed x.2 (v false) ∧ claimed p x g m v α H ε) →
        α true=α false := by
  classical
  let V := Label p.b× Finset (Tag p.g) × Bool
  have hp : 0<num V := by unfold num; positivity
  obtain ⟨ε,hε,hh⟩:= screen_calendar p (screenRank p K) M hM (num V*L) (by positivity)
    hr hj hg'
  refine ⟨ε,hε,?_⟩
  filter_upwards [hh] with n hn N U m hN w α g hw hk h
  by_contra he
  let S (i : V) (x : U) := i.2.1.card ≤ q ∧ screen p (onSide x i.2.2) i.1 i.2.1
    (screenRank p K) (g i.2.2) ε
  obtain ⟨i,hi⟩ : ∃ i,(num V)⁻¹≤ pr w (S i) := weighted_some hw S (fun x hx=>by
    obtain ⟨hd,v,H,hZ,hT,hV⟩:=h x hx
    obtain ⟨s,E,hE,t,hQ⟩:= unit_screen p K D q B hD hg hB m x hg' hj v α he
      (fun i=>(hZ i).2) hd hT H (fun i=>(hZ i).1) g ε hV
    exact ⟨(s,E,t),hE,hQ⟩)
  let E := i.2.1; let t := i.2.2
  let z := onW w (S i)
  have hi' := ((inv_pos_of_pos hp).trans_le hi)
  have hZ : IsLaw z := on_law hw.nz hi'
  let v := mapW z (fun x=>onSide x t)
  have hv (x) : v x ≤ num V*L*raw m N x := by
    have hx (i) : z i≤num V*w i := (on_mon hw.nz (inv_pos_of_pos hp) hi i).trans_eq
      (by rw [inv_inv])
    exact (mapW_cap hx (fun x=>onSide x t) _).trans
      (le_trans (mul_le_mul_of_nonneg_left (hk t x) hp.le) (le_of_eq (by ring)))
  have hB : E.card ≤ q := by
    obtain ⟨x,hx,_⟩:=exists_of_pr_pos hw.nz hi'
    exact hx.1
  apply hn m hN E (le_trans hs (by gcongr)) i.1 (g t) v (mapW_law hZ _) hv
  have hp : carried z (S i) := normW_carried (subW_carried w _)
  have hb : carried v (fun y => screen p y i.1 E (screenRank p K) (g t) ε) :=
    mapW_carried hp (fun x hx=> hx.2)
  exact fun i hi=>not_not.mp fun h=>hi (hb i h)
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

end PreparationParameters
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PhasePreparedOutcomes
attribute [-instance] _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype
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

set_option maxHeartbeats 1200000 in
theorem phaseAbsent_oai (hl : l≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in l,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in l,q.entered p (M*n) (m n) (w n) (s n))
    (hb : q.dosed l p M m w s b P)
    (he : ∀ᶠ n in l,(s n).within
      (fun x=> P n x → delta (b.m n) x=0)) :
    satisfied q l p M m w := by
  classical
  obtain ⟨d,h1,h2⟩:=hq.room
  have hB : q.B<Fintype.card (Label p.b) := by
    have he : (↑(Fintype.card (Label p.b)):ℝ) = bp ((p.b:ℕ):ℝ) := by simp [Label,bp_nat,F,ZMod.card]
    exact_mod_cast (hq.hB.trans_le ((bp_le (by linarith [(Nat.cast_nonneg p.j :
      0≤(p.j:ℝ))])).trans_eq he.symm))
  have hS : 0≤q.spear := mul_nonneg (bp_pos _).le hq.early.hL
  obtain ⟨ε,hε,h⟩:= silicon_calendar p M q.e q.D d q.B hq.hM h1 hq.hD hB hq.hJ hq.hg hq.hR
    h2 q.spear hS
  refine byTorch hl hq hw hx hb.cite ?_
  filter_upwards [hb.stake hl hq hw hx,hq.wrap.filter_mono hl,he,hx,hb.cite.mark,h.filter_mono hl,
    hb.cite.forecast.small ε hε,hb.capped]
    with n hn ht hv hx hs hh hδ hz
  let v:= potion s w P n
  have heq (x) (hh : v x≠0) :
      (rawHoles (m n)).unit x ∧ joins x≤2*q.D ∧ frameSide p (m n) x ∧
        delta (b.m n) x=0 ∧ engrave b q m s n x := by
    obtain ⟨hp,hx'⟩:= onW_ne hh
    obtain ⟨⟨i,hi,hx'⟩,_⟩:= LeafMixture.present hx'
    obtain ⟨_,h1,h2,h3⟩:= hx.onTile i hi x hx'
    exact ⟨h1,h2,h3,hv i hi x hx' hp,hs i hi x hx' hp⟩
  have hi : b.α true=b.α false := by
    refine hh _ ht.1 v b.α (fun i=>b.g i n) hn.1 hn.2.1 (fun x hc=>?_)
    obtain ⟨_,h2,h3,h4,⟨h5,h6⟩,_,_⟩:=heq x hc
    refine ⟨h2,b.m n x,b.L n x,fun i=> ⟨(h5 i).1,(effective_mem.mp (h5 i).2).1,
      hz x i,h3 i⟩, zero_delta (b.m n) x h4,?_⟩
    exact fun i z h l g => (h6 i z h l g).trans hδ
  have hm (x) (h : pairW v v x≠0) :
      matchProg b n x := by
    have hx := heq x.1 (left_ne_zero_of_mul h)
    have hy := heq x.2 (right_ne_zero_of_mul h)
    refine fade b.c b.α b.r hb.cite.forecast.light hi (fun HD => ?_) _ x hx.2.2.2.1 hy.2.2.2.1
    obtain ⟨he,_,hF,hD,⟨hg,_⟩,hh,hx⟩:=hx
    exact hh.symm.trans (delta_dusk (m n) (b.m n) _ (fun i=>(effective_mem.mp (hg i).2).1)
      (hx HD) hD he hF)
  have hi : charm s w P b n=pr (pairW v v) (fun _=>True) := avg_congr (fun i hi=>
    (ind_one (hm i hi)).trans ind_true.symm)
  have hv : IsLaw v:=hn.1
  rw [hi,pr_true,(pairW_law hv hv).total]; norm_num

end PreparationParameters
end HadwigerCounterexample

end

end OAI
end

theorem solution : type_of% @OAI.HadwigerCounterexample.PreparationParameters.phaseAbsent_oai := @OAI.HadwigerCounterexample.PreparationParameters.phaseAbsent_oai
