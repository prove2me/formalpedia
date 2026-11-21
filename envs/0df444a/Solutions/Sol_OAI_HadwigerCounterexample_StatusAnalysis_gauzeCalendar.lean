-- Prove2me | solution 1 for OAI.HadwigerCounterexample.StatusAnalysis.gauzeCalendar
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T23:06:25.788585+00:00
-- url     : https://prove2.me/submissions/6d3f460a-e2ec-4d5e-a7a2-1f55edae7282

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

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ComponentIndices
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch
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

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_MomentCoordinates
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
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

theorem card_row (p : Shape) (n : ℕ) :
    Fintype.card (Row p n) = psize p * (1 + (p.g*p.g+3)*n) := by
  simp [Row,AIdx,psize,add_comm]

variable (p : Shape)
variable {n : ℕ}

theorem point_base_eval (s : Label p.b) (z : Base p.g n) (r : AIdx p.g n) :
    point p s z (emptySel,r) = baseV z r := by simp [point,putLab,selV,emptySel]

variable {p}

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
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.flipZ_flip _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.reciprocal_actual _root_.OAI.HadwigerCounterexample.reciprocal_twice _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
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

theorem labMat_act (s) (z : Vec (AIdx p.g n)) :
    labMat p n s *ᵥ z = putLab p n s z := by
  funext i
  simp [Matrix.mulVec,dotProduct,labMat,putLab,monoBit,selV]

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

theorem move_exists_one {x y : Mat U I} (hx : Injective x.mulVec)
    (hy : Injective y.mulVec) : ∃ c : Move U, c.permMat I x = y := by
  let B := (0:Mat U Empty)
  let G := (0:Mat I Empty)
  have he {x : Mat U I} (hx : Injective x.mulVec) : gramGood G (x,B) :=
    ⟨Subsingleton.elim _ _, hx, fun a b _ => Subsingleton.elim a b⟩
  obtain ⟨c,hc⟩ := move_exists G _ _ (he hx) (he hy)
  exact ⟨c,congrArg Prod.fst hc⟩

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
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
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

theorem annih_annih (S : Space (Vec I)) : annih (annih S)=S := by
  symm
  have hh : S ≤ annih (annih S) := by
    intro x hx; rw [annih_mem]
    intro y hy; rw [dotProduct_comm]
    exact (annih_mem ..).mp hy _ hx
  refine Submodule.eq_of_le_of_finrank_eq hh ?_
  have he := annih_dim S
  have hg := annih_dim (annih S)
  change dim S=_

  exact Nat.add_right_cancel ((he.trans hg.symm).trans (Nat.add_comm ..))

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

open Filter

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_MatrixRankCounting
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.flipZ_flip _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.reciprocal_actual _root_.OAI.HadwigerCounterexample.reciprocal_twice _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
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

variable (p : Shape)

theorem nbr_profile_rank (K n : ℕ) :
    let d := Fintype.card (Row p n)
    nbr (fun M : Profile p n => totalRank M ≤ K) ≤
      (K+1:ℝ)^Fintype.card (Comp p.g) * bp (2*d*K) := by
  classical
  intro d
  let q (r : Comp p.g → Fin (K+1)) (M : Profile p n) :=
    (∑ i,(r i).val) ≤ K ∧ ∀ i, (M i).rank=(r i).val
  refine le_trans (nbr_le_sum _ q ?_) ?_
  · intro M h
    have hh i : (M i).rank≤K :=
      (Finset.single_le_sum (s:=Finset.univ) (fun i _ => Nat.zero_le ((M i).rank))
        (Finset.mem_univ i)).trans h
    exact ⟨fun i => ⟨_,Nat.lt_succ_of_le (hh i)⟩,h,fun _ => rfl⟩
  have he r : nbr (q r) ≤ bp (2*d*K) := by
    by_cases h : (∑ i:Comp p.g, (r i).val) ≤ K
    · unfold nbr
      let c (i : Comp p.g) (M : Moment p n) := (M.rank=(r i).val)
      simp_rw [q,h,true_and,ind_all]
      change tot (prodW (β:=fun _ => Moment p n) (fun i M => ind (c i M))) ≤ _
      rw [prodW_tot]
      have hx i : nbr (c i) ≤ bp (2*d*(r i).val) := by
        let w := (r i).val
        have h1 := nbr_matrix_rank (I:=Row p n) (J:=Row p n) w
        rw [← two_mul] at h1
        exact le_trans (tot_mono (fun x => ind_mono (p:=x.rank=w) (q:=x.rank≤w) (fun e => e.le))) h1
      refine (Finset.prod_le_prod (fun i _ => nbr_nonneg (c i)) (fun i _ => hx i)).trans ?_
      rw [←bp_sum,← Finset.mul_sum, ← Nat.cast_sum]
      apply bp_le
      gcongr
    · simp only [q,h,false_and,nbr,tot,ind_false,Finset.sum_const_zero]
      exact (bp_pos _).le
  refine (Finset.sum_le_sum fun i _ => he i).trans_eq ?_
  simp

open Filter
theorem profile_count (K : ℕ) :
    ∀ᶠ n : ℕ in atTop, nbr (fun M : Profile p n => totalRank M≤K) ≤ bp ((profileA p K:ℝ)*n) := by
  let B := (K+1:ℝ)^Fintype.card (Comp p.g)
  have h := bp_poly_dom_nat (a:=1) zero_lt_one B 0
  have h1 : 0 < psize p := Fintype.card_pos_iff.mpr ⟨emptySel⟩
  filter_upwards [h,eventually_ge_atTop 1] with n hn hN
  simp only [pow_zero,mul_one,one_mul] at hn
  refine le_trans (nbr_profile_rank p K n) (le_trans
    (mul_le_mul_of_nonneg_right hn.le (bp_pos _).le) ?_)
  rw [← bp_add]
  apply bp_le
  simp only [card_row, profileA]
  push_cast
  let s := psize p
  have he : 1 ≤ s := h1
  have h' :
      n+2*(s*(1+(p.g*p.g+3)*n))*K ≤ 10*(K+1)*s*(p.g*p.g+5)*n := by
    have hi : 1+(p.g*p.g+3)*n ≤ (p.g*p.g+4)*n := by nlinarith
    have hl : s*(1+(p.g*p.g+3)*n) ≤ s*((p.g*p.g+4)*n) := by gcongr
    have hh : n ≤ s*n := by nlinarith
    nlinarith only [Nat.mul_le_mul_right K hl,hh, Nat.zero_le (s*p.g*p.g*n),
      Nat.zero_le (s*n),Nat.zero_le (s*K*p.g*p.g*n),Nat.zero_le (s*K*n)]
  exact_mod_cast h'

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

theorem scopedZ_scan (p : Shape) (n l f x) (h : IsLaw (scopedScan p n l f x)) :
    mapW (scopedScan p n l f x) (freePart p)=unif :=
  fresh_Z p n _ (fun v y => by simp only [spin_scan_free]) h

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
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ProductCoordinateReplacement
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Product Coordinate Replacement -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Function
open scoped BigOperators
variable {I J K : Type} {A : Type} [Fintype I] [DecidableEq I] [Fintype A]

set_option maxHeartbeats 600000 in
theorem update_avg (p : I→ Wgt A) (i : I) (f : Wgt (I→A)) (hp : IsLaw (p i)) :
    avg (prodW p) f = avg (prodW p) (fun x => avg (p i) (fun y => f (update x i y))) := by
  classical

  let e : ((I→A)×A)≃ ((I→A)×A) := {
    toFun x := (update x.1 i x.2,x.1 i)
    invFun x := (update x.1 i x.2,x.1 i)
    left_inv x := by simp
    right_inv x := by simp }
  let μ := pairW (prodW p) (p i)
  have he (x : (I→A)×A) : μ (e x)=μ x := by
    unfold μ pairW prodW
    let s := Finset.univ.erase i
    rw [←Finset.mul_prod_erase _ _ (mem_univ i),←Finset.mul_prod_erase _
      (fun i => p i (x.1 i)) (mem_univ i)]
    have h :
        ∏ j∈s,p j (update x.1 i x.2 j)=∏ j∈s,p j (x.1 j) := by
      refine prod_congr rfl fun j hj => ?_
      rw [update_of_ne ((mem_erase.mp hj).1)]
    change p i _ * (∏ j∈s,p j (update x.1 i x.2 j))*p i (x.1 i)=_
    rw [h]
    change p i (Function.update x.1 i (x.2) i) * _ * _=_
    rw [Function.update_self]; ac_rfl
  have ht := avg_bij e μ (fun x => f x.1)
  simp_rw [he] at ht
  unfold μ at ht; simp only [pairW_avg,hp.avg_const] at ht
  exact ht.symm

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_BilinearBlockCorrelation
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bilinear Block Correlation -/

noncomputable section
namespace HadwigerCounterexample
open Finset LinearMap Module Matrix Function
open scoped BigOperators
variable {p : Shape} {I J A : Type} [Fintype I] [Fintype J] [Fintype A]
variable {n : ℕ}

theorem spring_update (p : Shape) (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (y : Knobs p.g n) (B) (h : f.keeps l B) (z : Vec (Fin n)) :
    spring p l s f (update y B z)= spring p l s f (update y B 0)+
      blockRay p n s B *ᵥ z := by
  classical
  have he : baseV (lit f l (update y B z))=baseV (lit f l (update y B 0))+blockA p n B *ᵥ z := by
    funext a
    rcases a with _|⟨d,j⟩
    · simp [baseV,blockA,mulVec,dotProduct,embedMat]
    by_cases hk : d=B
    · subst d; simp [baseV,blockA,mulVec,dotProduct,embedMat,lit,h]
    simp [baseV,blockA,mulVec,dotProduct,embedMat,lit,hk]
  unfold spring point blockRay
  rw [he,map_add,←Matrix.mulVec_mulVec,labMat_act]

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

theorem scanLaw (p : Shape) {n : ℕ} (l : Tag p.g) (z : Digest p.g)
    (f : Flavor p.g) (hr : 1 ≤ p.r) (hn : 2*p.r≤n) (h : z.feasible l f) :
    IsLaw (scopedScan p n l f z) := on_law (spins_law p n).nz
      ((scanPrice_pos p).trans_le (scan_fraction l f z hr hn h))
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FreeBlockLinearAction
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Free Block Linear Action -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Submodule Function Finset LinearMap
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

theorem blitz_pick (p : Shape) (M : Mat (Fin n) (Fin n)) (s : SelIdx p.b p.j)
    (B : Block p.g) (h : B≠Block.Z) (i : ℕ) :
    (blitz p M)ᵀ *ᵥ pick p n s B i=pick p n s B i := by
  classical
  apply sub_eq_zero.mp
  apply dot_ext_zero; intro x
  unfold pick
  split
  next hn =>
    rw [dotProduct_sub,dotProduct_transpose_mulVec,single_one_dotProduct,dotProduct_single,
      blitz_val]; simp [breeze,h]
  next => rw [Matrix.mulVec_zero,sub_zero,dotProduct_zero]

set_option maxHeartbeats 600000 in
theorem blitz_fixes (p : Shape) (M : Mat (Fin n) (Fin n)) (m : Mixer p n) :
    pullM (blitz p M) (blitz p M) (selfM p n m.mixM)=selfM p n m.mixM := by
  classical
  let T := blitz p M
  have h1 (i j : Tag p.g) : Block.O i j ≠ Block.Z := by simp [Block.O,Block.Z]
  have h2 : (@Block.S p.g) ≠ Block.Z := by simp [Block.S,Block.Z]
  have h3 : (@Block.sharp p.g) ≠ Block.Z := by simp [Block.sharp,Block.Z]
  have hh (B : Block p.g) (h : B ≠ Block.Z) :
      pullM T T (testM p n B)=testM p n B := by
    unfold pullM testM
    simp_rw [map_sum, liftM_outer, T,blitz_pick p M _ B h]
  have hr (a i) : Tᵀ*ᵥsharpPick p n a i=sharpPick p n a i := by
    unfold sharpPick
    split
    next h => exact blitz_pick p M _ _ h3 _
    next h => rw [Matrix.mulVec_zero]
  have ht :
      pullM T T (sharpM p n m.mixM)=sharpM p n m.mixM := by
    unfold sharpM pullM
    simp_rw [map_sum,map_smul,map_add,liftM_outer,hr,T,blitz_pick p M _ _ h3]
  unfold selfM
  simp_rw [map_add,map_sum]
  change ((∑ d:Tag p.g,∑ t:Tag p.g,pullM T T (testM p n (Block.O d t)))+
    pullM T T (testM p n Block.S))+pullM T T (sharpM p n m.mixM)=_
  rw [ht,hh _ h2]
  simp_rw [hh _ (h1 _ _)]

theorem sailsZ (p : Shape) (M : Mat (Fin n) (Fin n)) (x : Knobs p.g n)
    (l s f) :
    blitz p M *ᵥ spring p l s f x=spring p l s f (doZ p M x) := by
  classical
  rw [blitz_val]
  funext i; rcases i with ⟨i, _|⟨B,j⟩⟩
  · rfl
  by_cases h : B=Block.Z
  · subst B
    let a := selV p.j s i
    have he (x : Knobs p.g n) (v : Fin n) :
       spring p l s f x (i,some (Block.Z,v))=a*x Block.Z v := by
      simp [spring,point,putLab,baseV,a,lit,Flavor.keepZ]
    unfold breeze
    simp_rw [ite_true,he]
    let K := x Block.Z
    change (M *ᵥ (a • K)) j=a*doZ p M x Block.Z j
    rw [mulVec_smul]; simp [doZ,K]
  simp [breeze,spring,point,baseV,putLab,lit,doZ,h]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FrameRotations
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.Move.finiteMove _root_.OAI.HadwigerCounterexample.Move.identity_move _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Frame Rotations -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Function Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
namespace Move

variable (c : Flit n)

theorem boom_primary (y : Mat (Fin N) (Full p n)) :
    primary (fuse p c N y)=primary y*blitz p c.L ∧ channel (fuse p c N y)=channel y := by
  change primary (y*(boom p c).L)=_ ∧ channel (y*(boom p c).L)=_
  have hz : y*(boom p c).L = fromCols (primary y * blitz p c.L) (channel y) := by
    unfold boom
    conv_lhs => arg 1; rw [←fromCols_frame y]
    simp only [fromCols_mul_fromBlocks,Matrix.mul_zero,Matrix.mul_one,zero_add,add_zero]
  rw [hz]; exact ⟨rfl,rfl⟩

theorem fuse_inj (y : Mat (Fin N) (Full p n)) (h : Injective y.mulVec) :
    Injective (fuse p c N y).mulVec :=
  inj_comp_mat _ _ h (boom p c).L_inj

theorem kite_move (m : Mixer p n) {y : Oframe p n N}
    (h : FramesAt (gramCond m) y) :
    FramesAt (gramCond m) (fuse p c N y.1,fuse p c N y.2) := by
  obtain ⟨h1,h2,h3,h4,h5⟩ := (valid_iff ..).mpr h
  refine (valid_iff ..).mp ⟨c.fuse_inj _ h1,c.fuse_inj _ h2,?_,?_,?_⟩
  · have ha := (boom_primary c y.1).1; have hb := (boom_primary c y.2).1
    let B := blitz p c.L; let E := selfM p n m.mixM
    change (primary (fuse p c N y.1))ᵀ * primary (fuse p c N y.2)=_
    rw [ha,hb]
    calc _ =pullM B B E := by unfold E; rw [pullM_def,←h3,transpose_mul]; simp only [Matrix.mul_assoc,B]
         _ = E := blitz_fixes ..
  · change (channel (fuse p c N y.1))ᵀ * primary (fuse p c N y.2)=_
    rw [(boom_primary c y.1).2,(boom_primary c y.2).1,←Matrix.mul_assoc,h4,Matrix.zero_mul]
  change (primary (fuse p c N y.1))ᵀ*channel (fuse p c N y.2)=_
  rw [(boom_primary c y.1).1,(boom_primary c y.2).2,transpose_mul,Matrix.mul_assoc,
    h5,Matrix.mul_zero]

theorem kite_weights (m : Mixer p n) (x : Orient p n N) :
    raw m N (kite p c N x)=raw m N x := by
  unfold raw prodW
  refine Finset.prod_congr rfl fun i _ => ?_
  let A := (kite p c N x) i
  have h : FramesAt (gramCond m) A ↔ FramesAt (gramCond m) (x i) := by
    constructor
    · intro h
      have ht := kite_move c.sym m h
      have he : (fuse p c.sym N A.1,fuse p c.sym N A.2)=x i := Prod.ext ((fuse p c N).symm_apply_apply _) ((fuse p c N).symm_apply_apply _)
      rwa [he] at ht
    exact fun h => kite_move c m h
  simp only [unifOn_val]
  change ind (FramesAt _ A)/_=_
  rw [h]
theorem kite_keys (v : Template.Solo p) (x : Orient p n N) (z : Knobs p.g n) :
    v.desc z (kite p c N x)=v.desc (vault p c z) x := by
  let i := x
  let R (e : TagStar (v.t ())) (b : Bool) :
      takeSign (p:=p) ((kite p c N x) e.val) b = fuse p c N (takeSign (p:=p)
        (x e.val) b) := by cases b <;> rfl
  funext e b
  let w (z : Knobs p.g n) := spring p (v.t ()) (v.s ()) (v.f ()) z
  change primary _ *ᵥ w z = primary _ *ᵥ w _
  rw [R,(boom_primary c _).1,←mulVec_mulVec,sailsZ]
  rfl
end Move

theorem scannedZ (p : Shape) (l : Tag p.g) (f : Flavor p.g) (w : Knobs p.g n) (v : Vec (Fin n)) :
    scan p l f (update w Block.Z v)=scan p l f w := by
  classical
  funext i
  have h : asBlock i≠Block.Z := by rcases i with (⟨i,j⟩|_) <;> simp [asBlock]
  unfold scan; rw [update_of_ne h]

theorem scanned_flow (p : Shape) (n l f z) : flowZ p (scopedScan p n l f z) := by
  intro i j; simp only [scopedScan,onW_val,spins,← draws_unif,scannedZ,unif_apply]
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RandomLinearTransforms
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Random Linear Transforms -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Submodule Finset Function
open scoped BigOperators
variable {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype K] [DecidableEq K]

namespace Move

theorem flit_obs (M : Mat I J) (h : Injective M.mulVec) :
    mapW unif (fun c : Move I => c.L*M)=unifOn (fun A => Injective A.mulVec) := by
  classical
  rw [← unifOn_true]
  refine uniform_orbit _ (by obtain ⟨i⟩ := identity_move I; exact ⟨i,trivial⟩)
    (fun x _ => inj_comp_mat _ _ x.L_inj h) ?_
  intro x y hx hy
  obtain ⟨c,hc⟩ := move_exists_one hx hy
  refine ⟨circShift c,fun _ => Iff.rfl,fun w => ?_⟩
  change w.L*M=x ↔ c.L*w.L*M=y
  rw [←hc,Matrix.mul_assoc]; exact (c.permMat J).injective.eq_iff.symm

theorem flit_pmax (M Q : Mat I J) (h : Injective M.mulVec)
    (ha : num J-num I≤ -1) :
    pr unif (fun c : Move I => c.Rᵀ*M=Q) ≤ 2*bp (-num I*num J) := by
  let P (M : Mat I J) := Injective M.mulVec
  have ht :
      pr unif (fun c : Move I=> c.Rᵀ*M=Q)=unifOn P Q := by
    change pr unif (fun x : Move I => (flipLines I x).L*M=Q)=_
    rw [← mapW_pr unif (flipLines I) (fun c => c.L*M=Q),unif_equiv]
    exact congr_fun (flit_obs M h) Q
  have hh : 2⁻¹ ≤ pr unif P := by
    have hv := @unif_fail J I _ _ _ _
    rw [pr_not,unif_law.total] at hv
    have he := bp_le ha
    rw [bp_neg,bp_one] at he; change 1-pr unif P ≤ _ at hv; linarith only [hv,he]
  rw [ht,←on_unif]
  have he : unif Q=bp (-num I*num J) := by rw [unif_apply,neg_mul,bp_neg,←cast_mat]
  exact (on_mon unif_law.nz (show 0<(2:ℝ)⁻¹ from by norm_num) hh Q).trans_eq
    (by rw [he,inv_inv])

variable {n : ℕ}

theorem plume_dim (c : Flit n) (S : Space (Vec (Fin n))) : dim (plume c S)=dim S := by
  have hh := mrk_inj.mp (inj_comp_mat c.Rᵀ _ c.dual.L_inj (pack_inj S))
  rw [plume,colSp_dim,hh,Fintype.card_fin]

omit [Fintype I] [DecidableEq I] [DecidableEq J] [DecidableEq K] in
private theorem smaller_cols (P : Mat I J) (Q : Mat I K) (h : colSp P ≤ colSp Q) :
    ∃ M : Mat K J,Q*M=P := by
  classical
  choose f hf using fun i : J =>
    show ∃ z : Vec K,Q *ᵥ z=P.col i from h (colSp_mem i)
  refine ⟨Matrix.of (fun i j => f j i),?_⟩
  ext i j; exact congr_fun (hf j) i

set_option maxHeartbeats 800000 in
theorem plume_meets (n a : ℕ) (ha : a<n) (U V : Space (Vec (Fin n))) :
    pr unif (fun c : Flit n => a≤dim (c.plume U ⊓ V : Space (Vec (Fin n))))≤
      bp (1+((dim U:ℝ)+dim V-n)*a) := by
  classical
  let P := Mat (Fin (dim U)) (Fin a); let Q := Mat (Fin (dim V)) (Fin a)
  let S (z : P×Q) := pack U*z.1
  let q (p : P × Q) (c : Flit n) :=
    Injective (S p).mulVec∧c.Rᵀ*S p=pack V*p.2
  have hi (c : Flit n) (hc : a≤dim (c.plume U ⊓ V : Space (Vec (Fin n)))) :
      ∃ i,q i c := by
    let w := c.plume U⊓V
    obtain ⟨M,hM,hg⟩ := bounded_pack w a
    have he : Injective M.mulVec := mrk_inj.mpr (by
      rw [← colSp_dim,hg,Fintype.card_fin,min_eq_right hc])
    have hU := le_trans hM (show w ≤ c.plume U from inf_le_left)
    have hV : colSp M ≤ colSp (pack V) := by rw [colSp_pack]; exact le_trans hM inf_le_right
    obtain ⟨P,hp⟩ := smaller_cols _ _ hU
    obtain ⟨Q,hq⟩ := smaller_cols _ _ hV
    rw [Matrix.mul_assoc] at hp
    refine ⟨(P,Q),?_,hp.trans hq.symm⟩
    have hx (z : Vec (Fin a)) :
        c.Rᵀ*ᵥ((pack U * P)*ᵥz)= M*ᵥz := by rw [mulVec_mulVec,hp]
    intro i j hg; exact he ((hx i).symm.trans ((congrArg _ hg).trans (hx j)))
  have ht (i : P × Q) :
      pr unif (q i) ≤2*bp (-(n:ℝ)*a) := by
    by_cases h : Injective (S i).mulVec
    · unfold q; simp only [h,true_and]
      have hx : num (Fin a)-num (Fin n) ≤ -1 := by
        simp only [num,Fintype.card_fin]
        have hi : (a:ℝ)+1≤n := by exact_mod_cast ha
        linarith only [hi]
      simpa only [num,Fintype.card_fin] using flit_pmax (S i) (pack V*i.2) h hx
    simp only [q,h,false_and,pr_false]
    exact mul_nonneg (by norm_num) (bp_pos _).le
  refine (le_trans (pr_mono unif_law.nz hi) (pr_exists_le unif_law.nz q)).trans
    ((sum_le_sum (fun i _ => ht i)).trans_eq ?_)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_prod,Nat.cast_mul]
  change num P*num Q* _=_
  unfold P Q; rw [cast_mat,cast_mat,←bp_one,←bp_add,←bp_add,←bp_add]
  congr 1; simp only [num,Fintype.card_fin] <;> ring
end Move
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FreeBlockFourier
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Free Block Fourier -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Filter Function
open scoped BigOperators
variable {p : Shape} {n : ℕ} {I A : Type} [Fintype I] [DecidableEq I]
variable [Fintype A]

theorem zavg (p : Shape) (w : Wgt (Knobs p.g n)) (h : flowZ p w)
    (f : Wgt (Knobs p.g n)) :
    avg w f=avg w (fun x => avg unif (fun y => f (update x Block.Z y))) := by
  classical
  let A := Knobs p.g n
  let v : Wgt A := unif
  let k (f : Wgt A) (x : A) := f x * density v w x
  have he (f : Wgt A) : avg w f=avg v (k f) := by
    unfold avg; refine Finset.sum_congr rfl fun i _ => ?_
    have hv : v i ≠ 0 := by unfold v; rw [unif_apply]; positivity
    unfold k density
    field_simp
  let b : Block p.g→ Wgt (Vec (Fin n)) := fun _ => unif
  have hv : prodW b=v := draws_unif.symm
  rw [he f,he (fun _ => avg _ _), ← hv,update_avg b Block.Z (k f) unif_law]
  refine avg_congr fun i _ => ?_
  unfold k
  have ht (x) : density v w (update i Block.Z x)=density v w i := by
    unfold density; rw [h]; rfl
  simp_rw [ht,avg_mul]
  rfl

omit [DecidableEq I] in
private theorem vpsym (x y : Vec I) : vectorPhase x y=vectorPhase y x :=
  congrArg wsign (dotProduct_comm ..)
theorem hat_eqn (f : Wgt (Vec I)) (x : Vec I) :
    ∑ i:Vec I,(avg unif (fun y => vectorPhase i y*f y))*vectorPhase i x=f x := by
  classical
  unfold avg; simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hi y :
      ∑ i:Vec I,unif y*(vectorPhase i y*f y)*vectorPhase i x=
        ind (y=x)*f y := by
    rw [vector_expand]
    simp only [avg,Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [unif_apply,unif_apply]; ring
  simp_rw [hi]; simp [ind]

theorem z_atlas (p : Shape) (f : Wgt (Knobs p.g n)) (x) :
    zim p f univ x=f x := by
  unfold zim zchar zhat
  rw [hat_eqn (fun y => f (update x Block.Z y))]
  simp

theorem zhat_replay (p : Shape) (f : Wgt (Knobs p.g n)) (x) (y) (i) :
    zhat p f (update x Block.Z y) i= zhat p f x i := by simp [zhat]

theorem zchar_orth (p : Shape) (f g w : Wgt (Knobs p.g n)) (h : flowZ p w)
    (i j : Vec (Fin n)) (he : i≠j) :
    avg w (fun x => zchar p f i x * zchar p g j x)=0 := by
  rw [zavg p w h]
  have hh (x : Knobs p.g n) :
      avg unif (fun y => zchar p f i (update x Block.Z y)*zchar p g j (update x Block.Z y))=0 := by
    unfold zchar
    simp_rw [zhat_replay,update_self]
    have hi (x) : vectorPhase i x*vectorPhase j x = vectorPhase x i*vectorPhase x j := by
      rw [vpsym i,vpsym j]
    have ht (y : Vec (Fin n)) :
        zhat p f x i * vectorPhase i y * (zhat p g x j * vectorPhase j y) =
        zhat p f x i * zhat p g x j * (vectorPhase y i * vectorPhase y j) := by
      rw [←hi]; ring
    simp_rw [ht,avg_mul',←vector_expand,ind_zero he,mul_zero]
  simp_rw [hh,avg_zero]

theorem zsplit_orth (p : Shape) (f g w : Wgt (Knobs p.g n)) (h : flowZ p w)
    (s t : Finset (Vec (Fin n))) (hh : Disjoint s t) :
    avg w (fun x => zim p f s x*zim p g t x)=0 := by
  unfold zim; simp_rw [Finset.sum_mul,Finset.mul_sum,avg_sum]
  refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj =>
    zchar_orth p f g w h i j (fun e => Finset.disjoint_left.mp hh hi (e ▸ hj))

theorem zsplit_cost (p : Shape) (f w : Wgt (Knobs p.g n)) (h : flowZ p w)
    (hw : ∀ i, 0 ≤ w i) (s : Finset (Vec (Fin n))) :
    avg w (fun x => (zim p f s x)^2)≤avg w (fun x => f x^2) := by
  classical
  let t := univ\s
  let A := zim p f s; let B := zim p f t
  have hh x : f x^2 = A x^2+B x^2+2*(A x*B x) := by
    have he : A x+B x=f x := by
      unfold A B zim t
      rw [add_comm, Finset.sum_sdiff (subset_univ s)]; exact z_atlas p f x
    rw [← he]; ring
  have h0 := zsplit_orth p f f w h s t (Finset.disjoint_left.mpr (fun j hj hk =>
    (mem_sdiff.mp hk).2 hj))
  simp_rw [hh,avg_add,avg_mul',show avg w (fun x => A x*B x)=0 from h0,mul_zero,add_zero]
  exact le_add_of_nonneg_right (avg_nonneg hw (fun _ => sq_nonneg _))
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_QuadraticFourier
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
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

theorem half_power (x a : ℝ) (ha : x^2 ≤ bp a) : |x|≤ bp (a/2) :=
  le_of_pow_le_pow_left₀ (by decide : 2≠0) (bp_pos _).le (by
    rw [sq_abs,pow_two (bp _),←bp_add,show a/2+a/2=a by ring]; exact ha)

set_option maxHeartbeats 600000 in
theorem flare_rank (f : Vec I→F) (M : Mat I I) (h : polarize f M) :
    |avg unif (fun x => wsign (f x))| ≤ bp (-(M.rank:ℝ)/2) := by
  classical
  let g (x : Vec I) := wsign (f x)
  have hh :
      avg unif g ^ 2 = avg unif (fun x : Vec I => avg unif (fun y : Vec I =>
        g (x+y)*g y)) := by
    have hi (i : Vec I) : avg unif (fun x => g (x+i)*g i)=avg unif g*g i := by
      rw [avg_mul,phase_trans]
    rw [avg_avg]; simp_rw [hi,avg_mul']
    ring
  let L := Mᵀ
  have hg x y : g (x+y)*g y= wsign (f x+f 0)*wsign (dotL (L *ᵥ x) y) := by
    unfold g; rw [← wsign_add,← wsign_add,add_comm x y,h y x]
    unfold L
    congr 2
    change dotProduct x (M *ᵥ y)=dotProduct _ y
    rw [dotProduct_comm _ y,dotProduct_transpose_mulVec]
  have hi (x : Vec I) :
      avg unif (fun y : Vec I => g (x+y)*g y) ≤ ind ((L *ᵥ x)=0) := by
    simp_rw [hg x,avg_mul',wsign_lin]
    have he : dotL (L *ᵥ x)=0 ↔ L *ᵥ x=0 := by
      constructor
      · exact fun h => dot_ext_zero fun y => by rw [dotProduct_comm]; exact LinearMap.congr_fun h y
      intro h; rw [h]; exact LinearMap.ext (fun x => zero_dotProduct x)
    rw [he]
    exact (mul_le_mul_of_nonneg_right ((le_abs_self _).trans_eq (wsign_abs _))
      (ind_nonneg _)).trans_eq (one_mul _)
  refine half_power _ _ (?_)
  change avg unif g^2≤_
  rw [hh]
  refine (avg_mono unif_law.nz hi).trans_eq ?_
  have he : pr unif (fun x => L.mulVecLin x=0) = _ := pr_unif_lin L.mulVecLin 0
  rw [ind_one (LinearMap.range L.mulVecLin).zero_mem,one_mul] at he
  change pr unif _=_
  exact he.trans (by change bp (-(L.rank:ℝ))=_; rw [show L=Mᵀ from rfl,Matrix.rank_transpose])

omit [DecidableEq I] [DecidableEq J] in
theorem flare_affine (M : Mat J J) (P : Mat J I) (k : Vec J) (a : F) (i : Vec I) :
    let Q := fun x => dotProduct i x + (a + evmat M (P *ᵥ x+k) (P *ᵥ x+k))
    polarize Q (pullM P P (M+Mᵀ)) := by
  intro Q x y
  have he : dotProduct y ((pullM P P (M+Mᵀ)) *ᵥ x)=
      evmat M (P *ᵥ y) (P *ᵥ x) + evmat M (P *ᵥ x) (P *ᵥ y) := by
    change evmat _ _ _=_
    rw [evmat_pull,evmat_addM, evmat_transpose]
  rw [he]
  unfold Q evmat
  simp only [dotProduct_zero,Matrix.mulVec_zero,mulVec_add,dotProduct_add,add_dotProduct,
    zero_add]

  ring_nf
  simp only [mul_two,char_two,add_zero,zero_add]
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

theorem T0_scanZ (p : Shape) (hg : Odd p.g) (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (x : Profile p n) (u : Knobs p.g n) (y) :
    T0 p n x (useAtom p l s f (update u Block.Z y))=T0 p n x (useAtom p l s f u) := by
  simp_rw [T0_val,role_scan,roleT_scan]
  have h i : sharedT p n i (useAtom p l s f (update u Block.Z y))=sharedT p n i
      (useAtom p l s f u) := by rw [sharedT_scan p hg i,sharedT_scan p hg i]; simp only [scannedZ]
  simp_rw [h,scannedZ]

namespace Template

variable (v : Solo p)

theorem scroll_dim (v : Solo p) (m : Mixer p n) (x : Profile p n) :
    dim (scroll v m x) ≤ 2*(p.J*(p.g-1)*(2*totalRank x)) := by
  let P:=stave v n; let M:=slash v m x; let k:=p.J*(p.g-1)*(2*totalRank x)
  have hm : M.rank ≤ k := qmix_rank ..
  have h1 : dim (colSp (Pᵀ*M)) ≤ k := (Matrix.rank_mul_le_right ..).trans hm
  have h2 : dim (colSp (Pᵀ*Mᵀ)) ≤ k :=
    (Matrix.rank_mul_le_right ..).trans ((Matrix.rank_transpose _).le.trans hm)
  exact (Submodule.finrank_add_le_finrank_add_finrank ..).trans
    ((Nat.add_le_add h1 h2).trans_eq (two_mul _).symm)

theorem shanty_arc (v : Solo p) (m : Mixer p n) (x : Profile p n)
    (hg : Odd p.g) (u : Knobs p.g n) :
    let P := v.stave n; let M:= v.slash m x
    ∃ a : Ray p n,∃ b : F,∀ y,
      v.shanty m x (update u Block.Z y)=
        wsign (b + evmat M (P *ᵥ y+a) (P *ᵥ y+a)) := by
  intro P M
  let l := v.t (); let s := v.s (); let f := v.f ()
  let A := spring p l s f (update u Block.Z (0 : Vec (Fin n)))
  let b := T0 p n x (useAtom p l s f u)
  refine ⟨A,b,fun y => ?_⟩
  let t := update u Block.Z y
  let k := useAtom p l s f t
  have hx : Tsym m x k = T0 p n x k + evmat M (spring p l s f t) (spring p l s f t) := by
    unfold Tsym k useAtom; rw [LinearMap.add_apply,LinearMap.add_apply,Tmix_atom]
    exact congrArg (_ + ·) (mpair_outer ..)
  have ht : spring p l s f t=P *ᵥ y+A := (spring_update _ _ _ _ _ _ (Flavor.keepZ ..) _).trans
    (add_comm _ _)
  change wsign (Tsym m x k)=_
  rw [hx,ht]; unfold k t b
  rw [T0_scanZ p hg]

set_option maxHeartbeats 600000 in
theorem shanty_cap (v : Solo p) (m : Mixer p n) (x : Profile p n)
    (K s : ℕ) (hg : Odd p.g) (hm : unaryGood m K s) (hK : totalRank x≤K)
    (hx : 0<totalRank x) (u : Knobs p.g n) (i : Vec (Fin n)) :
    |zhat p (v.shanty m x) u i|≤bp (-((p.J-s:ℕ):ℝ)) := by
  classical
  obtain ⟨a,b,hab⟩ := shanty_arc v m x hg u
  let P := v.stave n; let M:= v.slash m x
  have hh := flare_affine M P a b i
  unfold zhat vectorPhase; simp_rw [hab,←wsign_add]
  have h : 2*((p.J-s:ℕ):ℝ)≤ (pullM P P (M+Mᵀ)).rank := by
    exact_mod_cast hm x (v.t ()) (v.s ()) hK hx
  exact (flare_rank _ (pullM P P (M+Mᵀ)) hh).trans (bp_le (by linarith only [h]))

set_option maxHeartbeats 800000 in
theorem shanty_outer (v : Solo p) (m : Mixer p n) (x : Profile p n) (u : Knobs p.g n)
    (hg : Odd p.g) (i : Vec (Fin n)) (hi : i∉scroll v m x) :
    zhat p (v.shanty m x) u i=0 := by
  classical
  let S:=scroll v m x; let P:=stave v n; let M:=slash v m x
  have hh : ∃ j∈annih S,dotProduct i j=1 := by
    by_contra! h
    apply hi
    rw [show v.scroll m x=S from rfl, ← annih_annih S]
    refine (annih_mem ..).mpr (fun j hj => (bit_cases _).resolve_right (h _ hj))
  obtain ⟨t,ht,he⟩ := hh
  let W y := v.shanty m x (update u Block.Z y)
  let C := P *ᵥ t
  have hz (y) : W (y+t)=W y := by
    obtain ⟨a,b,hQ⟩ := shanty_arc v m x hg u
    have hh (M : Moment p n) (h : colSp (Pᵀ*M)≤S) (i : Ray p n) :
        dotProduct C (M *ᵥ i)=0 := by
      have h1 := (annih_mem ..).mp ht _ (h (show (Pᵀ*M)*ᵥi∈_ from ⟨i,rfl⟩))
      rw [← mulVec_mulVec,dotProduct_transpose_mulVec] at h1; rw [dotProduct_comm]; exact h1
    let B := fun y => P *ᵥ y+a
    unfold W; simp_rw [hQ]
    change wsign (b+evmat M (B (y+t)) (B (y+t)))=_
    rw [show B (y+t)=B y+C by unfold B C; rw [mulVec_add]; ac_rfl]
    have h1 z : evmat M C z=0 := hh M le_sup_left z
    have h2 z : evmat M z C=0 := (evmat_transpose M _ _).symm.trans (hh Mᵀ le_sup_right z)
    unfold evmat at *
    simp_rw [mulVec_add,dotProduct_add,add_dotProduct,h1,h2]
    simp only [add_zero,B,P,M,mulVec_add,dotProduct_add,add_dotProduct]
  unfold zhat
  let Q (y) := vectorPhase i y*W y
  have hq (y) :
      Q (y+t) = Q y * (-1) := by unfold Q vectorPhase; rw [hz,dotProduct_add,wsign_add,he,wsign_one]; ring
  change avg unif Q=0
  have hh := phase_trans t Q
  simp_rw [hq] at hh; rw [avg_mul] at hh; linarith
end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ReindexedFourierSupport
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reindexed Fourier Support -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Submodule Function
open scoped BigOperators
variable {p : Shape} {n : ℕ} {I : Type} [Fintype I]

namespace Move
variable (c : Flit n) {j k : Vec (Fin n)}

theorem zhat_jump (p : Shape) (c : Flit n) (f : Wgt (Knobs p.g n)) (y : Knobs p.g n)
    (x : Vec (Fin n)) :
    zhat p (zreroute p c f) y (c.dual.jumpV x)=zhat p f y x := by
  classical
  unfold zhat
  rw [← avg_bij c.jumpV]
  have he (z : Vec (Fin n)) : unif (c.jumpV z)=unif z := rfl
  have hh (z) :
      vectorPhase (c.dual.jumpV x) (c.jumpV z)= vectorPhase x z := by
    unfold vectorPhase
    change wsign (dotProduct (c.Rᵀ *ᵥ x) (c.L *ᵥ z))=_
    rw [dotProduct_comm, dotProduct_transpose_mulVec,mulVec_mulVec,c.RL, Matrix.one_mulVec]
  have ht (z) :
      zreroute p c f (update y Block.Z (c.jumpV z))=f (update y Block.Z z) := by
    unfold zreroute vault; simp only [doZ,Equiv.coe_fn_symm_mk,update_self]
    change f (update (update y Block.Z _) _ (c.jumpV.symm (c.jumpV z)))=_
    rw [Equiv.symm_apply_apply]; simp
  simp_rw [he,hh,ht]

theorem jump_in (c : Flit n) (S : Space (Vec (Fin n))) {z} (h : z ∈ S) :
    c.dual.jumpV z∈c.plume S := by
  rw [←colSp_pack S] at h
  obtain ⟨u,h⟩ := h
  refine ⟨u,?_⟩
  change (c.Rᵀ*pack S)*ᵥu=c.dual.jumpV z
  rw [← mulVec_mulVec,show pack S *ᵥ u=z from h]
  rfl
end Move

namespace Template
variable (v : Solo p)

theorem rotor_budget (v : Solo p) (c : Flit n) (m : Mixer p n) (x : Profile p n)
    (K s : ℕ) (hg : Odd p.g) (hm : unaryGood m K s) (hK : totalRank x≤K) (hx : 0<totalRank x)
    (u : Knobs p.g n) (i : Vec (Fin n)) :
    |zchar p (v.rotor c m x) i u|≤bp (-((p.J-s:ℕ):ℝ)) ∧
    (i ∉ c.plume (v.scroll m x) → zchar p (v.rotor c m x) i u=0) := by
  classical
  obtain ⟨i,rfl⟩ := c.dual.jumpV.surjective i
  unfold zchar rotor
  rw [Move.zhat_jump,abs_mul,vectorPhase,wsign_abs,mul_one]
  exact ⟨shanty_cap v m x K s hg hm hK hx u i,fun h =>
    mul_eq_zero_of_left (shanty_outer v m x u hg i (fun he => h (Move.jump_in c _ he))) _⟩
end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_OrthogonalSpectrumBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Orthogonal Spectrum Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Submodule Function
open scoped BigOperators
variable {p : Shape} {n : ℕ}

theorem card_fieldRad (S : Space (Vec (Fin n))) : ((fieldRad S).card:ℝ)=bp (dim S) := by
  classical
  rw [←card_space]
  let e : S≃ (↑(fieldRad S) : Type) := {
    toFun x := ⟨x.val, by simp⟩
    invFun x := ⟨x.val,(mem_fieldRad ..).mp x.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  exact_mod_cast (Fintype.card_coe (fieldRad S)).symm.trans (Fintype.card_congr e).symm

set_option maxHeartbeats 800000 in
theorem clear_band (p : Shape) (w f : Wgt (Knobs p.g n)) (P : Knobs p.g n→Prop)
    (hw : IsLaw w) (hf : ∀ i, |f i|≤1) (h : flowZ p w)
    (b g : ℝ) (hb : 0≤b) (hq : g*pr w P≤ |zsumPeak p w f P|)
    (S T : Space (Vec (Fin n))) (s : ℕ) (hS : dim (S⊓T : Space (Vec (Fin n))) ≤ s)
    (hh : ∀ x i, |zchar p f i x|≤b ∧ (i∉T → zchar p f i x=0)) :
    ∃ (t : Finset (Vec (Fin n))) (a : ℝ), |a|=1 ∧
      (∀ i∈ t,i∉S ∧ i∈T) ∧
      let F i := a * zim p f t i
      (g-b*bp s)*pr w P ≤ zsumPeak p w F P ∧ avg w (fun i => F i ^ 2)≤1 := by
  classical
  let A := fieldRad T
  let B := fieldRad (S⊓T); let D := A\B
  have hB : B⊆A := fun i hi => (mem_fieldRad T i).mpr (((mem_fieldRad (S⊓T) i).mp hi).2)
  have he x : f x=zim p f D x+zim p f B x := by
    unfold zim D
    rw [Finset.sum_sdiff hB]
    change f x=∑ i∈A,_
    exact (z_atlas p f x).symm.trans (Finset.sum_subset (subset_univ A)
      (fun i _ hi=> (hh x i).2 (fun h => hi ((mem_fieldRad ..).mpr h)))).symm
  let V x := zsumPeak p w x P
  have hm (x) :
      |zim p f B x|≤b*bp s := by
    have hx : ((B.card:ℝ))≤bp s := le_trans (le_of_eq (card_fieldRad (S⊓T)))
      (bp_le (by exact_mod_cast hS))
    refine (abs_sum_le_sum_abs ..).trans ((Finset.sum_le_sum
      (s:=B) (fun i _ => (hh x i).1)).trans ?_)
    simp only [Finset.sum_const,nsmul_eq_mul,mul_comm b]
    exact mul_le_mul_of_nonneg_right hx hb
  have hz :
      |V (zim p f B)| ≤ b*bp s*pr w P := by
    apply (abs_avg_le hw.nz).trans
    have he (x : Knobs p.g n) :
        |ind (P x)*zim p f B x|≤ (b*bp s)*ind (P x) := by
      rw [abs_mul,abs_of_nonneg (ind_nonneg _),mul_comm (b*bp s)]
      exact mul_le_mul_of_nonneg_left (hm x) (ind_nonneg _)
    exact (avg_mono hw.nz he).trans_eq (avg_mul' ..)
  have h2 :
      |V f|≤|V (zim p f D)| + |V (zim p f B)| := by
    have ht :
        V f= V (zim p f D)+V (zim p f B) := by
      unfold V zsumPeak; rw [← avg_add]
      apply avg_congr; intro x _
      conv_lhs => rhs; rw [he x]
      rw [mul_add]
    rw [ht]; exact abs_add_le ..
  have hb :
      (g-b*bp s)*pr w P≤|V (zim p f D)| := by linarith only [hq,h2,hz]
  let a : ℝ := if 0≤ V (zim p f D) then 1 else -1
  have ha : |a|=1 := by unfold a; split <;> norm_num
  have hi :
      V (fun i=>a*zim p f D i) = |V (zim p f D)| := by
    have he (i : Knobs p.g n) : ind (P i)*(a*zim p f D i)=a*(ind (P i)*zim p f D i) := by ring
    have hh : V (fun i=>a*zim p f D i)=a*V (zim p f D) := by
      unfold V zsumPeak; simp_rw [he,avg_mul']
    rw [hh]; unfold a
    split
    next h => rw [one_mul,abs_of_nonneg h]
    next h => simp only [neg_mul,one_mul,abs_of_neg (lt_of_not_ge h)]
  refine ⟨D,a,ha,fun i hit => ?_,hb.trans_eq hi.symm,?_⟩
  · obtain ⟨h0,h1⟩ := mem_sdiff.mp hit
    obtain h2 := (mem_fieldRad ..).mp h0
    exact ⟨fun h => h1 ((mem_fieldRad (S⊓T) _).mpr ⟨h,h2⟩),h2⟩
  have ha' : a^2=1 := by rw [←sq_abs,ha]; norm_num
  simp_rw [mul_pow,ha',one_mul]
  exact (zsplit_cost p f w h hw.nz D).trans (hw.avg_le (fun i=>by
    have h := hf i
    nlinarith only [sq_abs (f i),abs_nonneg (f i),h]))
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_BiasedRotationBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Biased Rotation Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module Submodule Function LinearMap Filter Real
open scoped BigOperators
variable {p : Shape} {n : ℕ}

set_option maxHeartbeats 1200000 in
theorem spinning (p : Shape) (w : Wgt (Knobs p.g n))
    (f : Flit n→Wgt (Knobs p.g n)) (P : Knobs p.g n→Prop)
    (hw : IsLaw w) (hf : ∀ i j,|f i j|≤1) (h : flowZ p w)
    (b g δ : ℝ) (hb : 0≤b)
    (T : Space (Vec (Fin n))) (s l : ℕ) (hk : s<n)
    (hh : ∀ (c : Flit n) x i, |zchar p (f c) i x|≤b ∧
      (i∉ c.plume T → zchar p (f c) i x=0))
    (hδ : 0<δ) (ht : b*bp s < g) (hP : δ≤ pr w P)
    (hL : 1 < l * ((g-b*bp s)*δ)^2) :
    pr unif (fun c => g*pr w P ≤ |zsumPeak p w (f c) P|) ≤
      bp (1+((dim T:ℝ)+l*(dim T:ℝ)-n)*s) := by
  classical
  let M := g-b*bp s; have hM : 0<M := sub_pos.mpr ht
  let D c := g*pr w P ≤ |zsumPeak p w (f c) P|
  by_contra! H
  have progress (i : ℕ) (h' : i≤l) :
      ∃ (S : Space (Vec (Fin n))) (U : Wgt (Knobs p.g n)),
        zsafe p w U S ∧ dim S≤ i*dim T ∧ i*(M*δ) ≤ zsumPeak p w U P ∧
          avg w (fun x=>U x ^ 2) ≤ i := by
    induction i with
    | zero =>
      refine ⟨⊥,fun _=>0,?_,?_,?_,?_⟩
      · intro i t h; simp only [zero_mul,avg_zero]
      · simp [dim]
      · simp [zsumPeak,avg_zero]
      simp only [zero_pow (by decide : 2 ≠ 0),avg_zero,Nat.cast_zero,le_refl]
    | succ i ih =>
      obtain ⟨S,U,hS,hU,h1,h2⟩ := ih (by omega)
      let Q (c : Flit n) := s < dim (c.plume T ⊓ S : Space (Vec (Fin n)))
      have hh' : ∃ c : Flit n, D c ∧ ¬ Q c := by
        by_contra! hh
        have hz := (pr_mono unif_law.nz (fun c (h : D c) =>
          (hh c h).le)).trans (Move.plume_meets n s hk T S)
        have hy : (dim S:ℝ)≤ l*(dim T:ℝ) := by
          exact_mod_cast (hU.trans (Nat.mul_le_mul_right _ (by omega) : i*dim T ≤ l*dim T))
        apply (not_lt_of_ge (le_trans hz (bp_le ?_))) H
        nlinarith only [mul_le_mul_of_nonneg_right hy (Nat.cast_nonneg s : 0≤(s:ℝ))]
      obtain ⟨c,he,hc⟩ := hh'
      let W := c.plume T
      have hk : dim (S ⊓ W : Space (Vec (Fin n))) ≤ s := by
        have hh : dim (W⊓S : Space (Vec (Fin n))) ≤ s := le_of_not_gt hc
        rw [inf_comm]; exact hh
      obtain ⟨t,a,ha,hA,hy,hz⟩ := clear_band p w (f c) P hw (hf c) h b g hb he S W s hk (hh c)
      let Z i := a*zim p (f c) t i
      let C i := U i+Z i
      have hQ : avg w (fun i=>U i * Z i)=0 := by
        have he := hS (f c) t (fun i hi => (hA i hi).1)
        unfold Z; simp_rw [mul_left_comm _ a,avg_mul',he,mul_zero]
      refine ⟨S ⊔ W,C,?_,?_,?_,?_⟩
      · intro i s hh
        have hL := zsplit_orth p (f c) i w h t s (Finset.disjoint_left.mpr (fun j hj he =>
          hh j he ((show W≤S⊔W from le_sup_right) (hA j hj).2)))
        have he := hS i s (fun j hj h => hh j hj ((show S≤S⊔W from le_sup_left) h))
        unfold C Z; simp only [add_mul,mul_assoc,avg_add,avg_mul',he,hL,mul_zero,add_zero]
      · have h := Submodule.finrank_add_le_finrank_add_finrank S W
        refine le_trans h ?_
        change dim S+dim W≤_
        unfold W; rw [Move.plume_dim c T,Nat.add_mul,one_mul]
        omega
      · unfold zsumPeak C; simp_rw [mul_add,avg_add]
        change _≤zsumPeak p w U P+zsumPeak p w Z P
        change M*pr w P ≤ zsumPeak p w Z P at hy
        push_cast
        nlinarith only [h1,hy,mul_le_mul_of_nonneg_left hP hM.le]
      · have hh (i) : C i^2=U i^2+Z i^2+2*(U i*Z i) := by unfold C; ring
        simp_rw [hh,avg_add,avg_mul',hQ,mul_zero,add_zero]
        exact (add_le_add h2 hz).trans_eq (by push_cast; rfl)
  obtain ⟨S,U,_,_,hu,hq⟩ := progress l (le_refl _)
  have hh : ↑l * (M*δ) ≤ zsumPeak p w U P := hu
  have hx :
      zsumPeak p w U P ^2 ≤ l := by
    apply (avg_CS hw.nz (fun i=>ind (P i)) U).trans
    have hz (i : Knobs p.g n) : ind (P i)^2 ≤ 1 :=
      calc ind (P i)^2 ≤ 1^2 := pow_le_pow_left₀ (ind_nonneg _) (ind_le_one _) _
           _ = _ := one_pow _
    exact (mul_le_mul (hw.avg_le hz) hq (avg_nonneg hw.nz (fun _ => sq_nonneg _))
      zero_le_one).trans_eq (one_mul _)
  have hy := pow_le_pow_left₀ (by positivity) hh 2
  change 1<↑l*(M*δ)^2 at hL
  have hl : 0<l := by
    by_contra! he
    obtain rfl : l=0 := by omega
    norm_num at hL
  nlinarith only [hx,hy,mul_lt_mul_of_pos_left hL
    (Nat.cast_pos.mpr hl : (0:ℝ) < l)]

namespace Template
variable {K s A : ℕ}
theorem rotor_levels (v : Solo p) (K s a : ℕ)
    (hs : 2*a < s) (hg : Odd p.g)
    (δ g : ℝ) (hδ : 0<δ)
    (hG : bp (-((p.J-s:ℕ):ℝ))*bp s < g) :
    ∀ᶠ n : ℕ in atTop, ∀ m : Mixer p n, unaryGood m K s →
      ∀ x : Profile p n, 0<totalRank x → totalRank x ≤ K →
      ∀ w : Wgt (Knobs p.g n), IsLaw w → flowZ p w →
      ∀ P : Knobs p.g n → Prop, δ ≤ pr w P →
      pr unif (fun c => g*pr w P ≤|zsumPeak p w (v.rotor c m x) P|) ≤ bp (-(2*a:ℝ)*n) := by
  classical
  let b := bp (-((p.J-s:ℕ):ℝ))
  have hb : b*bp s<g := hG
  let t := ((g-b*bp s)*δ)^2
  have ht : 0<t := by apply pow_pos (mul_pos (sub_pos.mpr hb) hδ)
  obtain ⟨l,hl⟩ := exists_nat_gt (1/t)
  let d := 2*(p.J*(p.g-1)*(2*K))
  have ha : 0<(s:ℝ)-2*a := sub_pos.mpr (by exact_mod_cast hs)
  have hz : Tendsto (fun n:ℕ => (↑s-2*a:ℝ)*n) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos ha).mpr tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop s,hz.eventually (eventually_ge_atTop
    (1+((d:ℝ)+l*d)*s))] with n hn hN m hm x hx hK w hw hh P hP
  have he := spinning p w (fun c=>v.rotor c m x) P hw (by
    intro i j; unfold rotor Move.zreroute shanty; rw [wsign_abs]) hh b g δ
    (bp_pos _).le _ s l hn (fun c y i => v.rotor_budget c m x K s hg hm hK hx y i)
    hδ hb hP ((div_lt_iff₀ ht).mp hl)
  apply he.trans
  apply bp_le
  have hy :
      dim (v.scroll m x) ≤ d :=
    (scroll_dim v m x).trans (by unfold d; gcongr)
  have hx : ((dim (v.scroll m x)):ℝ) ≤ d := by exact_mod_cast hy
  change 1+((d:ℝ)+l*d)*s≤ ((s:ℝ)-2*a)*n at hN
  have hB := mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg l : 0≤(l:ℝ))
  nlinarith only [mul_le_mul_of_nonneg_right (add_le_add hx hB)
    (Nat.cast_nonneg s : 0≤(s:ℝ)),hN]
end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_OrientationRankBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Orientation Rank Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Submodule Function Filter Real
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
namespace Template
variable (v : Solo p)
variable {K s : ℕ}

theorem beat_round (v : Solo p) (P : AtomKey (p:=p) (v.t ()) N →Prop) (o : Orient p n N)
    (w f : Wgt (Knobs p.g n)) (hw : flowZ p w) (c : Flit n) :
    zsumPeak p w f (offBeat v P (Move.kite p c N o)) =
      zsumPeak p w (Move.zreroute p c f) (offBeat v P o) := by
  classical
  unfold zsumPeak offBeat
  have hh (y : Knobs p.g n) : w (Move.vault p c y)=w y := hw y _
  conv_rhs => rw [← avg_bij (Move.vault p c)]
  simp_rw [hh,Move.kite_keys,Move.zreroute,Equiv.symm_apply_apply]
theorem beat_morph (v : Solo p) (P : AtomKey (p:=p) (v.t ()) N →Prop) (o : Orient p n N)
    (w : Wgt (Knobs p.g n)) (hw : flowZ p w) (c : Flit n) :
    pr w (offBeat v P (Move.kite p c N o)) = pr w (offBeat v P o) := by
  have h := beat_round v P o w (fun _=>1) hw c
  simp only [zsumPeak,Move.zreroute,mul_one] at h
  exact h

set_option maxHeartbeats 800000 in
theorem radiance_calendar (v : Solo p)
    (hs : 2*profileA p K < s) (hg : Odd p.g)
    (δ g : ℝ) (hδ : 0<δ)
    (hG : bp (-((p.J-s:ℕ):ℝ))*bp s < g) :
    ∀ᶠ n : ℕ in atTop,∀ (N : ℕ),2*num (Full p n)<N →
      ∀ m : Mixer p n, unaryGood m K s →
      ∀ w : Wgt (Knobs p.g n), IsLaw w → flowZ p w →
      ∀ P : AtomKey (p:=p) (v.t ()) N → Prop,
      pr (raw m N) (fun o => ∃ x, 0<totalRank x ∧ totalRank x≤ K ∧ v.glow m w P g δ x o) ≤
        bp (-(profileA p K:ℝ)*n) := by
  classical
  let d := profileA p K
  filter_upwards [rotor_levels v _ _ _ hs hg δ g hδ hG,profile_count p K]
    with n hn ht N hN m hM w hw h P
  let μ := raw m N
  let F x := v.glow m w P g δ x
  let L (x : Profile p n) := totalRank x≤K
  have hμ := raw_law m hN
  let b := bp (-(2*d:ℝ)*n)
  have h1 (x : Profile p n) (he : L x) (hy : 0<totalRank x) :
      pr μ (F x)≤b := by
    have hi (o : Orient p n N) :
        pr unif (fun c => F x (Move.kite p c N o))≤b := by
      unfold F glow
      simp_rw [beat_round _ _ _ _ _ h,beat_morph _ _ _ _ h]
      let f := offBeat v P o
      by_cases hb : δ≤pr w f
      · change pr unif (fun c => δ≤pr w f ∧ _)≤_
        simp only [hb,true_and]
        exact hn m hM x hy he w hw h f hb
      change pr unif (fun c => δ≤pr w f ∧ _)≤_
      simp only [hb,false_and,pr_false]; exact (bp_pos _).le
    have hz (c : Flit n) :
        pr μ (F x)=pr μ (fun o => F x (Move.kite p c N o)) := by
      unfold pr μ
      conv_lhs => rw [← avg_bij (Move.kite p c N)]
      simp_rw [Move.kite_weights]
    have hh :
        pr μ (F x)=avg unif (fun c => pr μ (fun o => F x (Move.kite p c N o))) := by
      simp_rw [←hz]; exact (unif_law.avg_const _).symm
    rw [hh]
    unfold pr; rw [avg_avg]; exact hμ.avg_le hi
  let Q (x : Profile p n) (o : Orient p n N) := 0<totalRank x∧L x∧F x o
  have hi x : pr μ (Q x)≤ ind (L x)*b := by
    by_cases he : L x
    · by_cases hx : 0<totalRank x
      · simpa only [Q,he,ind_true,one_mul,hx,true_and] using h1 x he hx
      simp only [Q,hx,false_and,he,true_and,pr_false,ind_true,one_mul]; exact (bp_pos _).le
    simp only [Q,he,false_and,and_false,ind_false,zero_mul,pr_false,le_refl]
  apply (pr_exists_le hμ.nz Q).trans
  refine (Finset.sum_le_sum (fun i _ => hi i)).trans ?_
  rw [← Finset.sum_mul]; change nbr L*b ≤ _
  refine (mul_le_mul_of_nonneg_right ht (bp_pos _).le).trans_eq ?_
  unfold d; rw [←bp_add]; congr 1; ring
end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_BasisConditioning
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Basis Conditioning -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Finset Filter Function
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]

theorem totalRank_pos {x : Profile p n} (h : x≠0) :
    0<totalRank x := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp h
  apply lt_of_lt_of_le _ (Finset.single_le_sum (fun i _=>Nat.zero_le ((x i).rank))
    (Finset.mem_univ i))
  apply Nat.pos_of_ne_zero; intro h
  obtain ⟨A,B,hh⟩ := mul_factor (x i) 0 h.le
  apply hi; ext a b; rw [←hh,Matrix.mul_apply]; simp

theorem glint_within {K d : ℕ} (h : d≤ K^2) :
    glintRate K ≤ (1/8:ℝ)*bp (- (d:ℝ)) := by
  unfold glintRate
  have hh : bp (-3)=1/8 := by norm_num [bp]
  rw [←hh,←bp_add]
  exact bp_le (by linarith only [(show (d:ℝ) ≤ ((K^2:ℕ):ℝ) from by exact_mod_cast h)])

namespace Template
variable (v : Solo p)

theorem staining (m : Mixer p n) (f : Vec I→ₗ[F] Profile p n) (z : Knobs p.g n) (i : Vec I) :
    vectorPhase i (stains v m f z)=shanty v m (f i) z := by
  classical
  let h := LinearMap.flip (Tsym m) (useAtom p (v.t ()) (v.s ()) (v.f ()) z) ∘ₗ f
  have ht : h i=h (∑ j: I,i j • (Pi.single j 1 : Vec I)) := by
    have he (j:I) : i j • (Pi.single j 1 : Vec I)=Pi.single j (i j) := by
      funext k; by_cases hh:k=j <;> simp [hh]
    simp_rw [he]
    rw [Finset.univ_sum_single]
  change wsign (∑ j:I,i j*h (Pi.single j 1))=wsign (h i)
  rw [ht,map_sum]; simp_rw [map_smul]; rfl

set_option maxHeartbeats 800000 in
theorem glow_luminous (v : Solo p) (m : Mixer p n) (w : Wgt (Knobs p.g n))
    (hw : IsLaw w)
    (S : AtomKey (p:=p) (v.t ()) N → Prop)
    (K : ℕ) (i : Orient p n N) (δ : ℝ) (hδ : 0<δ) (he : δ ≤ pr w (offBeat v S i))
    (h : ∀ x, 0<totalRank x → totalRank x≤K → ¬ glow v m w S (glintRate K) δ x i) :
    luminous v m w S K i := by
  classical
  let P := offBeat v S i
  have hP : 0<pr w P := hδ.trans_le he
  let u := onW w P; have hu : IsLaw u := on_law hw.nz hP
  refine ⟨hP,fun d hd f hf hg x => ?_⟩
  let s := stains v m f
  have heq :
      pr u (fun z => s z=x) = avg unif (fun i => vectorPhase i x*
          avg u (fun z => vectorPhase i (s z))) := by
    unfold pr
    simp_rw [vector_expand]
    rw [avg_avg]
    apply avg_congr
    intro i hi
    rw [avg_mul]; ring
  let b := bp (-(d:ℝ))
  let Q (k : Vec (Fin d)) := vectorPhase k x * avg u (fun z => vectorPhase k (s z))
  have hb : 0 < b := bp_pos _
  have hh k : ind (k=0)-b/8 ≤ Q k := by
    by_cases hk : k=0
    · subst k
      have hQ : Q 0=1 := by unfold Q; simp only [vectorPhase,zero_dotProduct,wsign_zero,one_mul,
        hu.avg_const]
      rw [ind_one (show (0:Vec (Fin d))=0 from rfl),hQ]; linarith
    let k' := f k
    have hT := h k' (totalRank_pos (hf.ne hk |>.trans_eq (map_zero f))) (hg k)
    have hz : |zsumPeak p w (v.shanty m k') P| ≤ (glintRate K)*pr w P :=
      le_of_lt (lt_of_not_ge (fun h => hT ⟨he,h⟩))
    have ht :
        avg u (fun z => vectorPhase k (s z))=
          zsumPeak p w (v.shanty m k') P/pr w P := by
      unfold s u onW; simp_rw [staining]; rw [avg_norm,subW_tot]
      congr 1; simp [zsumPeak,avg,subW,mul_assoc,k']
    have h1 : |Q k|≤b/8 := by
      unfold Q; rw [ht,abs_mul,vectorPhase,wsign_abs,one_mul,abs_div,abs_of_pos hP]
      refine le_trans ((div_le_iff₀ hP).mpr hz) ((glint_within hd).trans_eq (by unfold b; ring))
    rw [ind_zero hk,zero_sub]; exact (abs_le.mp h1).1
  have h0 : unif (0:Vec (Fin d))=b := by
    unfold b; rw [unif_apply,card_space,dim_vec,bp_neg,Fintype.card_fin]
  change _ ≤ pr u (fun z => s z=x)
  rw [heq]
  refine le_trans ?_ (avg_mono unif_law.nz hh)
  rw [avg_sub,unif_law.avg_const,
    show avg unif (fun i : Vec (Fin d)=> ind (i=0))=b from (pr_point' unif _).trans h0]
  change 7/8*b≤_
  linarith
end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_UnaryPositivityBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unary Positivity Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Function Filter
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
namespace Template
variable (v : Solo p)

variable {K s : ℕ}
set_option maxHeartbeats 1200000 in
theorem patrolled (v : Solo p) (M : ℕ) (hM : 1≤M) (hg : Odd p.g) (hj : 1≤p.j)
    (z : Digest p.g) (hz : z.feasible (v.t ()) (v.f ())) (hr : 1≤p.r)
    (η : ℝ) (hη : 0<η)
    (hs : 2*profileA p K < s) (hG : bp (-((p.J-s:ℕ):ℝ))*bp s < glintRate K) :
    ∀ᶠ n : ℕ in atTop, let N := M*n
    let w:=scopedScan p n (v.t ()) (v.f ()) z; let q:=z.sumBit
    ∀ m : Mixer p n, unaryGood m K s →2*num (Full p n)<N →
    ∀ S,η ≤ pr (lawOmega p N (v.t ()) q) S →
    pr (raw m N) (fun x => ¬ patrol v m w S K q x) ≤ bp (-(1/16:ℝ)*n) := by
  classical
  let δ := 3/4*η; have hδ : 0<δ := by positivity
  let ε := η/4; have hε : 0<ε := by positivity
  filter_upwards [radiance_calendar v hs hg δ _ hδ hG,
    flat_recital v M hM hj ε hε,eventually_ge_atTop (2*p.r),
    pay_nat (a:=1/8) (b:=1/16) 2 (by norm_num)]
    with n hn hF hU ha N w q m hm hN S hS
  let μ := raw m N
  have hμ : IsLaw μ := raw_law m hN
  let P := offBeat (n:=n) v S
  let T (i : AtomKey (p:=p) (v.t ()) N) := ind (S i)
  have hw : IsLaw w := scanLaw p _ _ _ hr hU hz
  have he :
      carried w (fun x => dialed p (v.t ()) (v.f ()) x=q) := fun i hi => by
    unfold w scopedScan; rw [onW_val,ind_zero (show ¬ _ from fun h =>
      hi (congrArg Digest.sumBit h)),mul_zero,zero_div]
  have ht (x) : |T x|≤1 := by rw [abs_of_nonneg (ind_nonneg (S x))]; exact ind_le_one _
  have hx := hF m w q hw he (scopedZ_scan p n _ _ _ hw) hN T ht
  have hy := hn N hN m hm w hw (scanned_flow p n (v.t ()) (v.f ()) z) S
  let b := pr (lawOmega p N (v.t ()) q) S
  let X (x) := ε ≤ |pr w (P x)-b|
  let Y (x) := ∃ i, 0<totalRank i ∧ totalRank i≤K ∧ glow v m w S (glintRate K) δ i x
  have hi i (h : ¬patrol v m w S K q i) : X i ∨ Y i := by
    by_contra! hh
    have hr : 3/4*b≤pr w (P i) := by
      have ht := lt_of_not_ge hh.1
      change |pr w (P i)-b|<ε at ht
      have hz := (abs_lt.mp ht).1
      unfold ε at *; change η≤b at hS; linarith only [hz,hS]
    have hd : δ ≤ pr w (P i) := le_trans (mul_le_mul_of_nonneg_left hS (by norm_num)) hr
    exact h ⟨glow_luminous v m w hw S K i δ hδ hd (fun z h1 h2 h3 => hh.2 ⟨z,h1,h2,h3⟩),hr⟩
  apply (le_trans (pr_mono hμ.nz hi) (pr_or_le hμ.nz)).trans
  have h1 : pr μ X≤ bp (-(1/8:ℝ)*n) := le_trans (le_of_eq (by
    unfold X P b minorCall offBeat T; simp only [pr]; rfl)) hx
  apply (add_le_add h1 hy).trans
  have he : (1:ℝ) ≤ profileA p K := by
    have hi : 1≤psize p := Fintype.card_pos_iff.mpr ⟨emptySel⟩
    have hP : 0 < profileA p K := by unfold profileA; exact Nat.mul_pos (Nat.mul_pos (by omega) hi) (by omega)
    exact_mod_cast (show 1≤profileA p K from hP)
  rw [two_mul] at ha
  refine le_trans ?_ ha
  gcongr; linarith

end Template
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

end Appearance

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CellPositivityScales
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cell Positivity Scales -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix Function
open scoped BigOperators Topology
variable {p:Shape} {n N K M r : ℕ}
namespace StatusAnalysis
open Template
variable {b : PreparationParameters}

namespace Appearance
variable (x : Appearance p) {s0 : ℕ}

theorem readCap (x : Appearance p) (r M : ℕ) (h : AnalyticParameters p M b s0)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, let N:=M*n; ∀ m : Mixer p n,2*num (Full p n)<(N:ℝ) →
    ∀ Y : Silhouette p N r,pr (raw m N) (fun o=> x.apt∧¬ x.close Y o ε)≤bp (-(1/16:ℝ)*n) := by
  classical
  have hp:=h.enter.first
  by_cases ha : x.apt
  · let δ : ℝ := ε/(r+1:ℝ)
    have hδ : 0<δ:=by unfold δ; positivity
    filter_upwards [flat_recital x.trot M hp.hM hp.hJ δ hδ,eventually_ge_atTop (2*p.r),
      pay_nat (a:=1/8) (b:=1/16) (num (Fin r)) (by norm_num)] with n hn ht hB N m hN Y
    let w:= x.wit n; let v:= raw m N
    have hw : IsLaw w:= witLaw ha hp.hR ht
    let P (i : Fin r) (o : Orient p n N):=
      δ≤ |x.empirical Y o i - x.reference Y i|
    have hk (i : Fin r) : pr v (P i) ≤ bp (-(1/8:ℝ)*n) := by
      let S (z) := ind (Y x.l x.q z=i)
      have hf z : |S z|≤1 := by unfold S; rw [abs_of_nonneg (ind_nonneg _)]; exact ind_le_one _
      refine hn m w x.q hw (normW_carried (subW_carried _ _))
        (scopedZ_bit p n _ _ _ hw) hN S hf
    have he (o : Orient p n N) (h : x.apt∧¬x.close Y o ε) : ∃ i,P i o := by
      by_contra! hh
      apply h.2
      unfold close varOne
      calc _ ≤ ∑ i : Fin r,δ:= Finset.sum_le_sum fun i _=>le_trans (abs_sub_comm ..).le
             (le_of_not_ge (hh i))
           _ ≤ ε := by
             simp; unfold δ
             calc _ ≤ ((r:ℝ)+1)* (ε/(r+1:ℝ)) := mul_le_mul_of_nonneg_right (by linarith) hδ.le
                  _ = ε := by field_simp
    have hv : IsLaw v:= raw_law m hN
    exact ((pr_mono hv.nz he).trans (pr_exists_le hv.nz P)).trans
      (((Finset.sum_le_sum fun i _=>hk i).trans_eq (by simp [num])).trans hB)
  filter_upwards with n N m hN Y
  simp_rw [show (x.apt)=False from eq_false ha,false_and,pr_false]; exact (bp_pos _).le

theorem foilCap (x : Appearance p) (r M : ℕ) (h : AnalyticParameters p M b s0)
    (δ:ℝ) (hδ:0<δ) :
    ∀ᶠ n : ℕ in atTop, let N:=M*n; ∀ m : Mixer p n,2*num (Full p n)<(N:ℝ) →
      unaryGood m b.pins s0 → ∀ Y: Silhouette p N r,
      pr (raw m N) (fun i=>¬x.foil Y i m b.pins δ)≤bp (-(1/18:ℝ)*n) := by
  classical
  have ht:=h.enter.first
  let A:= Digest p.g × Fin r
  let Q n (m:Mixer p n) (Y:Silhouette p (M*n) r) (a : A) (o : Orient p n (M*n)) :=
    a.1.feasible x.l x.f ∧ a.1.sumBit=x.q ∧ δ≤x.reference Y a.2 ∧
      ¬Template.patrol x.trot m (scopedScan p n x.l x.f a.1)
        (fun y=>Y x.l x.q y=a.2) b.pins x.q o
  have hg (a:A) :
      ∀ᶠ n:ℕ in atTop,let N:=M*n;∀ m:Mixer p n,2*num (Full p n)<(N:ℝ) →
        unaryGood m b.pins s0→∀ Y:Silhouette p N r,
          pr (raw m N) (Q n m Y a) ≤ bp (-(1/16:ℝ)*n) := by
    by_cases hf : a.1.feasible x.l x.f ∧ a.1.sumBit=x.q
    · filter_upwards [patrolled x.trot M ht.hM ht.hg ht.hJ a.1 hf.1 ht.hR δ hδ h.profiles
        h.gleaming] with n hn N m hN hM Y
      by_cases he : δ ≤ x.reference Y a.2
      · let S : AtomKey (p:=p) (x.trot.t ()) (M*n) →Prop := fun i=>Y x.l x.q i=a.2
        let v:=scopedScan p n (x.trot.t ()) (x.trot.f ()) a.1
        have hx : δ ≤ pr (lawOmega p (M*n) (x.trot.t ()) a.1.sumBit) S := by
          rw [hf.2]; exact he
        have hh (i:Orient p n (M*n)) (h:Q n m Y a i) :
            ¬Template.patrol x.trot m v S b.pins a.1.sumBit i := hf.2 ▸ h.2.2.2
        exact (pr_mono (raw_law m hN).nz hh).trans (hn m hM hN S hx)
      have hg : Q n m Y a=fun _=> False :=
        funext fun i=> eq_false (fun h=>he h.2.2.1)
      change pr (raw m (M*n)) (Q n m Y a) ≤ _
      rw [hg,pr_false]; exact (bp_pos _).le
    filter_upwards with n N m hN hg Y
    have hh : Q n m Y a=fun _=> False :=
      funext fun i=> eq_false (fun h=> hf ⟨h.1,h.2.1⟩)
    change pr (raw m (M*n)) (Q n m Y a) ≤ _
    rw [hh,pr_false]; exact (bp_pos _).le
  filter_upwards [eventually_all.mpr hg,pay_nat (a:=1/16) (b:=1/18) (num A) (by norm_num)]
    with n hn hB N m hN hM Y
  have he o (h : ¬x.foil Y o m b.pins δ) : ∃ i, Q n m Y i o := by
    unfold foil at h
    push Not at h
    obtain ⟨z,i,h⟩:=h
    exact ⟨(z,i),h⟩
  let v:=raw m N
  have hv : IsLaw v:=raw_law m hN
  exact ((pr_mono hv.nz he).trans (pr_exists_le hv.nz _)).trans
    (((Finset.sum_le_sum fun i _=>hn i m hN hM Y).trans_eq (by simp [num])).trans hB)
end Appearance

variable {s0 : ℕ}

private theorem silken (p : Shape) (r M : ℕ) (h : AnalyticParameters p M b s0)
    (ε δ : ℝ) (he:0<ε) (hd:0<δ) :
    ∀ᶠ n : ℕ in atTop, let N:=M*n; ∀ m : Mixer p n,2*num (Full p n)<(N:ℝ) →
      unaryGood m b.pins s0 → ∀ Y: Silhouette p N r,
      pr (raw m N) (fun i=>¬smoothSilk p ε δ Y m b.pins i)≤bp (-(1/20:ℝ)*n) := by
  classical
  let A:= Appearance p
  filter_upwards [eventually_all.mpr (fun x:A=>x.foilCap r M h δ hd),
    eventually_all.mpr (fun x:A=>x.readCap r M h ε he),
    pay_nat (a:=1/18) (b:=1/20) (num A*2) (by norm_num)] with n hn ht hB N m hN hM Y
  let v:=raw m N
  have hv : IsLaw v:=raw_law m hN
  let P (x:A) (o:Orient p n N) :=
    (x.apt ∧ ¬x.close Y o ε)∨ ¬x.foil Y o m b.pins δ
  have hk x : pr v (P x) ≤ 2*bp (-(1/18:ℝ)*n) := by
    rw [two_mul]; apply (pr_or_le hv.nz).trans
    refine add_le_add ((ht x m hN Y).trans (bp_le ?_)) (hn x m hN hM Y)
    linarith [(Nat.cast_nonneg n :0≤(n:ℝ))]
  have hi o (h : ¬smoothSilk p ε δ Y m b.pins o) : ∃ i, P i o := by
    unfold smoothSilk at h
    obtain ⟨i,h⟩:= Classical.not_forall.mp h
    exact ⟨i,by unfold P; tauto⟩
  refine ((pr_mono hv.nz hi).trans (pr_exists_le hv.nz _)).trans
    (((Finset.sum_le_sum fun i _=>hk i).trans_eq ?_).trans hB)
  simp [num,mul_assoc]

theorem gauzeCalendar_oai (p : Shape) (r M : ℕ) (h : AnalyticParameters p M b s0)
    (ε δ:ℝ) (he:0<ε) (hd:0<δ) :
    ∀ᶠ n : ℕ in atTop, let N:=M*n; ∀ m : Mixer p n,∀ u : Wgt (UnitType p n N),
      PreparationParameters.Align b s0 p M n m u → ∀ Y: Silhouette p N r,
      pr u (fun i=>¬gauze p ε δ Y m b.pins i)≤bp (-(1/100:ℝ)*n) := by
  classical
  filter_upwards [silken p r M h ε δ he hd,pay_nat (a:=1/20-1/32) (b:=1/100) 2
    (by norm_num)] with n hn ht N m u hu Y
  let P (o:Orient p n N) := ¬smoothSilk p ε δ Y m b.pins o
  let Q (i:Bool) (o:UnitType p n N):=P (onSide o i)
  have hc : bySide p u m (bp ((1/32:ℝ)*n)) := fun i=> by
    have hh:= hu.drain
    cases i; exact hh.2.2.1; exact hh.2.1
  have hf : ∀ i,pr u (Q i) ≤bp (-((1/20:ℝ)-1/32)*n) := by
    intro i
    let x := fun o:UnitType p n N=>onSide o i
    change pr u (fun i=>P (x i)) ≤_
    rw [←mapW_pr]
    exact (pr_cap (hc i) P).trans ((mul_le_mul_of_nonneg_left
      (hn m hu.cols hu.hymn Y) (bp_pos _).le).trans_eq (by rw [←bp_add]; congr 1; ring))
  have he o (h : ¬gauze p ε δ Y m b.pins o) : ∃ i,Q i o := Classical.not_forall.mp h
  have hv : IsLaw u:=hu.drain.1
  rw [two_mul] at ht
  refine ((pr_mono hv.nz he).trans ((pr_exists_le hv.nz _).trans ?_))
  rw [Fintype.sum_bool]; exact (add_le_add (hf _) (hf _)).trans ht

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

theorem solution : type_of% @OAI.HadwigerCounterexample.StatusAnalysis.gauzeCalendar_oai := @OAI.HadwigerCounterexample.StatusAnalysis.gauzeCalendar_oai
