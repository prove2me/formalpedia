-- Prove2me | solution 1 for OAI.ElementaryPositivity.TriangularDynamics.triangularLinear_locality
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T19:00:56.154812+00:00
-- url     : https://prove2.me/submissions/be12b10d-6b08-4e08-86a5-46f7b176beef

import Mathlib
import Definitions.Def_OAIQ368Chrom058
import Theorems.Thm_OAI_ElementaryPositivity_TriangularDynamics_genuine_history_cut_deficit

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_TorusContinuity
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instAddCommGroup _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries LaurentPrecision ElementaryPositivity.PowerSeriesSplit
noncomputable section
variable {M I ι : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ)
variable (C : (I → ℤ) →+ M) (l : Filter ι)
attribute [local instance] Classical.propDecidable

local instance instAddGroupTorusLaurentSeriesRat_rdb4876_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instSubTorusLaurentSeriesRat
lemma torus_mul_finite (S T : Finset M) (f g : Torus v Ω)
    (hf : f.support⊆S) (hg : g.support⊆T) (m : M) :
    (f*g) m=∑x∈S,∑y∈T,
      (Finsupp.single (x+y) (f x*g y*(↑(v^(Ω x y)) : LaurentSeries ℚ)) : Torus v Ω) m := by
  change Torus.multiply v Ω f g m=_
  unfold Torus.multiply
  rw [Finsupp.sum_of_support_subset f hf _ (by intros; simp)]
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finsupp.sum_of_support_subset g hg _ (by intros; simp),Finsupp.finsetSum_apply]

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TorusPositive
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries LaurentPrecision
noncomputable section
variable {M I ι : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ)
variable (C : (I→ℤ) →+ M) (l : Filter ι)
attribute [local instance] Classical.propDecidable

local instance instAddGroupTorusLaurentSeriesRat_3_rdb4876_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instSubTorusLaurentSeriesRat_3_rdb4876_1 : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
lemma torus_mul_support (S T : Finset M) (f g : Torus v Ω)
    (hf : f.support⊆S) (hg : g.support⊆T) : (f*g).support⊆sumSupport S T := by
  intro m hm
  by_contra H
  apply Finsupp.mem_support_iff.mp hm
  rw [torus_mul_finite v Ω S T f g hf hg m]
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  apply Finsupp.single_eq_of_ne
  intro Hxy
  apply H
  exact Finset.mem_image.mpr ⟨(x,y),Finset.mem_product.mpr ⟨hx,hy⟩,Hxy.symm⟩

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_HomogeneousElementaryExpressions
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open Classical
noncomputable section

variable {M V:Type*} [AddCommGroup M] [Fintype V] [DecidableEq V]
variable (v:(LaurentSeries ℚ)ˣ) (Ω:M →+ M →+ ℤ)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.homogeneousElementaryExpressionsRing
local instance homogeneousElementaryExpressionsAddCommMonoid_rdb4876_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.homogeneousElementaryExpressionsAddGroup
lemma cutSupported_zero (ell:M →+ ℤ) (N:ℤ) : CutSupported v Ω ell N 0 := by
  simp [CutSupported]
lemma cutSupported_one (ell:M →+ ℤ) : CutSupported v Ω ell 0 1 := by
  intro m hm
  change m∈(Finsupp.single 0 (1:LaurentSeries ℚ)).support at hm
  have hh:m=0:=by simpa using hm
  subst m
  simp
lemma cutSupported_add (ell:M →+ ℤ) (N:ℤ) {F G:Torus v Ω}
    (hF:CutSupported v Ω ell N F) (hG:CutSupported v Ω ell N G) : CutSupported v Ω ell N (F+G) := by
  intro m hm
  rcases Finset.mem_union.mp (Finsupp.support_add hm) with hf|hg
  · exact hF m hf
  · exact hG m hg
lemma cutSupported_neg (ell:M →+ ℤ) (N:ℤ) {F:Torus v Ω}
    (hF:CutSupported v Ω ell N F) : CutSupported v Ω ell N (-F) := by
  intro m hm
  exact hF m (by simpa using hm)
lemma cutSupported_mul (ell:M →+ ℤ) (A B:ℤ) {F G:Torus v Ω}
    (hF:CutSupported v Ω ell A F) (hG:CutSupported v Ω ell B G) : CutSupported v Ω ell (A+B) (F*G) := by
  intro m hm
  have hh:=torus_mul_support v Ω F.support G.support F G (by rfl) (by rfl) hm
  obtain ⟨⟨a,b⟩,hab,rfl⟩:=Finset.mem_image.mp hh
  obtain ⟨ha,hb⟩:=Finset.mem_product.mp hab
  simpa only [map_add] using add_le_add (hF a ha) (hG b hb)

open RationalFiber
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_ElementaryExpressionBounds
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open Classical
open WallUnits
noncomputable section
variable {M V:Type*} [AddCommGroup M] [Fintype V] [DecidableEq V]
variable (v:(LaurentSeries ℚ)ˣ) (Ω:M →+ M →+ ℤ)

local instance elementaryExpressionBoundsRing_rdb4876_1 : Ring (Torus v Ω) := Torus.instRing v Ω
local instance elementaryExpressionBoundsAddCommMonoid_rdb4876_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance elementaryExpressionBoundsAddGroup_rdb4876_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
lemma independentElement_cutSupported_scaled (ell:M →+ ℤ) (K:ℤ) (w:V → M)
    (hw:∀x,ell (w x) ≤ K) (k:ℕ) : CutSupported v Ω ell ((k:ℤ)*K) (independentElement v Ω w k) := by
  intro m hm
  have hn:independentElement v Ω w k m≠0:=Finsupp.mem_support_iff.mp hm
  simp only [independentElement,Finsupp.finsetSum_apply] at hn
  obtain ⟨s,_,hs⟩:=Finset.exists_ne_zero_of_sum_ne_zero hn
  unfold independentTerm at hs
  split_ifs at hs with hc
  · have hms:m=∑x∈s,w x:=by
      by_contra h
      exact hs (Finsupp.single_eq_of_ne h)
    rw [hms,map_sum]
    calc
      ∑x∈s,ell (w x) ≤ ∑_x∈s,K := Finset.sum_le_sum fun x _=>hw x
      _ = (k:ℤ)*K := by simp [hc.2]
  · exact (hs rfl).elim

lemma ElementaryExpr.cutSupported_scaled {k:ℕ} (f:ElementaryExpr k) (ell:M →+ ℤ) (K:ℤ)
    (w:V → M) (hw:∀x,ell (w x) ≤ K) : CutSupported v Ω ell ((k:ℤ)*K) (f.eval v Ω w) := by
  induction f with
  | zero k => exact cutSupported_zero v Ω ell _
  | one => simpa [eval] using cutSupported_one v Ω ell
  | atom k => exact independentElement_cutSupported_scaled v Ω ell K w hw k
  | add f g hf hg => exact cutSupported_add v Ω ell _ hf hg
  | neg f hf => exact cutSupported_neg v Ω ell _ hf
  | mul f g hf hg => simpa only [eval,Nat.cast_add,add_mul] using cutSupported_mul v Ω ell _ _ hf hg

lemma ElementaryExpr.weight {k:ℕ} (f:ElementaryExpr k) (ell:M →+ ℤ) (K:ℤ)
    (w:V → M) (hw:∀x,ell (w x)=K) (m:M) (hm:m∈(f.eval v Ω w).support) : ell m=(k:ℤ)*K := by
  have h1:=f.cutSupported_scaled v Ω ell K w (fun x=>(hw x).le) m hm
  have h2:=f.cutSupported_scaled v Ω (-ell) (-K) w (fun x=>by simp [hw x]) m hm
  change -ell m ≤ (k:ℤ)*(-K) at h2
  linarith
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_IncomingEquality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {M : Type*} [AddCommGroup M]
variable (Ω : M →+ M →+ ℤ) (p : M) (hp : Ω p p=0)

lemma mutationIncomingLabel_nonnegative (m : M) (hm : 0≤Ω p m) : mutationIncomingLabel Ω p m=m := by
  rw [mutationIncomingLabel,max_eq_left (by omega),zero_zsmul,add_zero]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RationalPureCoefficients
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instRingTorus
local instance instAddCommMonoidTorus_1_rdb4876_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_3_rdb4876_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instNonUnitalSemiringTorus_rdb4876_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_rdb4876_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
lemma mul_X_coeff (f : Torus v Ω) (r m : M) :
    (f*Torus.X v Ω m) (r+m)=f r*(↑(v^(Ω r m)):K) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>simp only [add_mul,Finsupp.add_apply,hf,hg]
  | single t a=>
    change (Torus.monomial v Ω t a*Torus.monomial v Ω m 1) (r+m)=_
    rw [Torus.monomial_mul_monomial]
    by_cases ht : t=r
    · subst t; simp [Torus.monomial]
    · simp [Torus.monomial,Ne.symm ht]

lemma X_mul_coeff (f : Torus v Ω) (r m : M) :
    (Torus.X v Ω m*f) (r+m)=f r*(↑(v^(Ω m r)):K) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>simpa only [mul_add,Finsupp.add_apply,hf,hg] using (_root_.add_mul (f r) (g r) _).symm
  | single t a=>
    change (Torus.monomial v Ω m 1*Torus.monomial v Ω t a) (r+m)=_
    rw [Torus.monomial_mul_monomial]
    by_cases ht : t=r
    · subst t; simp [Torus.monomial,add_comm]
    · have hmt : m+t≠r+m:=by intro hh; apply ht; simpa only [add_comm m t,add_right_cancel_iff] using hh
      simp [Torus.monomial,Ne.symm ht,Ne.symm hmt]

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_MonomialConjugation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {K M:Type*} [Field K] [AddCommGroup M]
variable (v:Kˣ) (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)

include hΩ
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.monomialConjugationRing
local instance monomialConjugationAddCommMonoid_rdb4876_1 : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance monomialConjugationAddGroup_rdb4876_1 : AddGroup (Torus v Ω) :=
  (Torus.instRing v Ω).toAddGroup
lemma X_mul_X_neg (b:M) : Torus.X v Ω b*Torus.X v Ω (-b)=1 := by
  rw [Torus.X_mul_X_of_pairing_zero v Ω b (-b) (by simp only [map_neg,hΩ,neg_zero])]
  simp only [add_neg_cancel]
  rfl

lemma monomialConjugate_coeff (b:M) (f:PowerSeries (Torus v Ω)) (n:ℕ) (r:M) :
    coeff n (monomialConjugate v Ω b f) r=coeff n f r*(↑(v^(2*Ω b r)):K) := by
  rw [monomialConjugate,coeff_mul_C,coeff_C_mul]
  have H:=mul_X_coeff v Ω (Torus.X v Ω b*coeff n f) (r+b) (-b)
  rw [add_neg_cancel_right,X_mul_coeff] at H
  rw [H,map_add,AddMonoidHom.add_apply,map_neg,map_neg,hΩ,neg_zero,add_zero,
    alternating_skew Ω hΩ r b,neg_neg,mul_assoc,←Units.val_mul,←zpow_add]
  congr 3
  ring

end
end ElementaryPositivity.QuantumTorus
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I]
variable (v:(LaurentSeries ℚ)ˣ) (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
include hΩ in
lemma monomialConjugate_graded (C:(I → ℤ) →+ M) (b:M) {f:PowerSeries (Torus v Ω)}
    (hf:SeriesGraded v Ω C f) : SeriesGraded v Ω C (monomialConjugate v Ω b f) := by
  intro n m hm
  rw [monomialConjugate_coeff v Ω hΩ,hf n m hm,zero_mul]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_NormalizedMonomialAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint
noncomputable section
variable {K M:Type*} [Field K] [AddCommGroup M]
variable (v:Kˣ) (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instRingTorus_1
local instance instAddCommMonoidTorus_2_rdb4876_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_4_rdb4876_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
include hΩ in
lemma adjoint_monomial_normalized (f:PowerSeries (Torus v Ω)) (b:M) :
    adjoint f (PowerSeries.C (Torus.X v Ω b))=
      normalizedMonomialAction v Ω f b*PowerSeries.C (Torus.X v Ω b) := by
  have H:PowerSeries.C (Torus.X v Ω (-b))*PowerSeries.C (Torus.X v Ω b)=
      (1:PowerSeries (Torus v Ω)):=by
    rw [←map_mul]
    simpa only [neg_neg,map_one] using congrArg
      (PowerSeries.C : Torus v Ω → PowerSeries (Torus v Ω)) (X_mul_X_neg v Ω hΩ (-b))
  simp only [normalizedMonomialAction,monomialConjugate,adjoint,mul_assoc,H,mul_one]

include hΩ in
lemma adjoint_monomial_coeff (f:PowerSeries (Torus v Ω)) (b r:M) (n:ℕ) :
    coeff n (adjoint f (PowerSeries.C (Torus.X v Ω b))) (r+b)=
      coeff n (normalizedMonomialAction v Ω f b) r*(↑(v^(Ω r b)):K) := by
  rw [adjoint_monomial_normalized v Ω hΩ,coeff_mul_C,mul_X_coeff]
end
end ElementaryPositivity.QuantumTorus
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I]
variable (v:(LaurentSeries ℚ)ˣ) (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
include hΩ in
lemma normalizedMonomialAction_graded (C:(I → ℤ) →+ M) (f:CompletedPositive v Ω C) (b:M) :
    SeriesGraded v Ω C (normalizedMonomialAction v Ω f.val b) :=
  SeriesGraded.mul v Ω C f.property.2 (monomialConjugate_graded v Ω hΩ C b
    (SeriesGraded.inverse v Ω C f.property.2))
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_LatticeHahn
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instAddCommGroup _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries HahnSeries PowerSeriesAdjoint
noncomputable section
variable {R M:Type*} [CommRing R] [AddCommGroup M]
variable (v:Rˣ) (Ω:M →+ M →+ ℤ) (τ:M →+ ℤ)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.latticeHahnRing
local instance latticeHahnAddCommMonoid_rdb4876_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance latticeHahnAddGroup_rdb4876_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.latticeHahnNonUnitalSemiring
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.latticeHahnNonUnitalNonAssocSemiring
lemma latticeHahn_monomial (b:M) (c:R) :
    latticeHahn v Ω τ (Torus.monomial v Ω b c)=
      HahnSeries.single (τ b) (Torus.monomial v Ω b c) := by
  change constantCoeff (laurentHomogenize v Ω 0 τ (Torus.monomial v Ω b c))=_
  rw [laurentHomogenize_monomial]
  simp only [AddMonoidHom.zero_apply,Int.toNat_zero,monomial_zero_eq_C_apply,constantCoeff_C]

lemma latticeHahn_coeff (F:Torus v Ω) (j:ℤ) (m:M) :
    (latticeHahn v Ω τ F).coeff j m=if j=τ m then F m else 0 := by
  change (constantCoeff (laurentHomogenize v Ω 0 τ F)).coeff j m=_
  rw [←coeff_zero_eq_constantCoeff,laurentHomogenize_coeff]
  simp

lemma hahn_single_shift_adjoint (f:PowerSeries (Torus v Ω)) (j:ℤ) (F:Torus v Ω) :
    HahnSeries.ofPowerSeries ℤ (Torus v Ω) f * HahnSeries.single j F *
      HahnSeries.ofPowerSeries ℤ (Torus v Ω) (invOfUnit f 1)=
    HahnSeries.single j (1:Torus v Ω)*
      HahnSeries.ofPowerSeries ℤ (Torus v Ω) (adjoint f (PowerSeries.C F)) := by
  have H (g:HahnSeries ℤ (Torus v Ω)):
      g*HahnSeries.single j (1:Torus v Ω)=HahnSeries.single j (1:Torus v Ω)*g:=by
    apply HahnSeries.ext
    funext n
    rw [HahnSeries.coeff_mul_single,HahnSeries.coeff_single_mul,mul_one,one_mul]
  rw [adjoint,map_mul,map_mul,HahnSeries.ofPowerSeries_C]
  have HS:HahnSeries.single j F=HahnSeries.single j (1:Torus v Ω)*HahnSeries.C F:=by
    change HahnSeries.single j F=HahnSeries.single j (1:Torus v Ω)*HahnSeries.single 0 F
    rw [HahnSeries.single_mul_single,add_zero,one_mul]
  rw [HS,←mul_assoc,H, mul_assoc,mul_assoc,mul_assoc]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_PolynomialAdjointCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d) (pc:I)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.polynomialAdjointCoefficientsRing
local instance polynomialAdjointCoefficientsAddCommMonoid_rdb4876_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance polynomialAdjointCoefficientsAddGroup_rdb4876_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
lemma actualPolynomialAdjointCoefficient_add (τ:M →+ ℤ) (f:PowerSeries (Torus LaurentRay.vUnit Ω))
    (F G:Torus LaurentRay.vUnit Ω) (m:M) :
    actualPolynomialAdjointCoefficient Ω τ f (F+G) m=
      actualPolynomialAdjointCoefficient Ω τ f F m+actualPolynomialAdjointCoefficient Ω τ f G m := by
  exact Finsupp.sum_add_index' (fun _=>zero_mul _) (fun _ _ _=>add_mul _ _ _)

lemma actualPolynomialAdjointCoefficient_monomial (τ:M →+ ℤ)
    (f:PowerSeries (Torus LaurentRay.vUnit Ω)) (b m:M) (c:LaurentSeries ℚ) :
    actualPolynomialAdjointCoefficient Ω τ f (Torus.monomial LaurentRay.vUnit Ω b c) m=
      c*actualMonomialAdjointCoefficient Ω τ f b m := by
  exact Finsupp.sum_single_index (zero_mul _)

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_PureActualCoefficients
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits RationalFiber
noncomputable section
variable {M:Type*} [AddCommGroup M]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (τ:M →+ ℤ)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.pureActualCoefficientsRing
local instance pureActualCoefficientsAddCommMonoid_rdb4876_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance pureActualCoefficientsAddGroup_rdb4876_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
include hΩ in
lemma actualMonomialAdjointCoefficient_read (f:PowerSeries (Torus LaurentRay.vUnit Ω)) (b m:M) :
    actualMonomialAdjointCoefficient Ω τ f b m=
      if 0≤τ (m-b) then
        coeff (τ (m-b)).toNat (adjoint f (PowerSeries.C (Torus.X LaurentRay.vUnit Ω b))) m else 0 := by
  unfold actualMonomialAdjointCoefficient actualRootCoefficient
  split_ifs with h
  · simpa only [sub_add_cancel] using
      (adjoint_monomial_coeff LaurentRay.vUnit Ω hΩ f b (m-b) (τ (m-b)).toNat).symm
  · exact zero_mul _

end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.PowerSeriesAdjoint
open PowerSeries HahnSeries
noncomputable section
variable {A:Type*} [Ring A]
lemma hahnAction_add (f:PowerSeries A) (x y:HahnSeries ℤ A) :
    hahnAction f (x+y)=hahnAction f x+hahnAction f y := by
  simp only [hahnAction,mul_add,add_mul]
lemma hahnAction_zero (f:PowerSeries A) : hahnAction f (0:HahnSeries ℤ A)=0 := by
  simp only [hahnAction,mul_zero,zero_mul]
lemma hahnAction_one (x:HahnSeries ℤ A) : hahnAction 1 x=x := by
  have hi:invOfUnit (1:PowerSeries A) 1=1:=by simpa using mul_invOfUnit (1:PowerSeries A) 1 (by simp)
  simp only [hahnAction,hi,map_one,one_mul,mul_one]
lemma ofPowerSeries_coeff_int (f:PowerSeries A) (j:ℤ) :
    (ofPowerSeries ℤ A f).coeff j=if 0≤j then coeff j.toNat f else 0 := by
  by_cases hj:0≤j
  · rw [ite_eq_left hj,←Int.toNat_of_nonneg hj,HahnSeries.ofPowerSeries_apply_coeff,Int.toNat_natCast]
  · rw [ite_eq_right hj,HahnSeries.ofPowerSeries_apply]
    apply HahnSeries.embDomain_notin_image_support
    rintro ⟨n,_,hn⟩
    have he:(n:ℤ)=j:=hn
    omega
end
end ElementaryPositivity.PowerSeriesAdjoint
namespace ElementaryPositivity.QuantumTorus
open PowerSeries HahnSeries PowerSeriesAdjoint WallUnits
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0) (τ:M →+ ℤ)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.pureActualScalarCoefficientsRing
local instance pureActualScalarCoefficientsAddCommMonoid_rdb4876_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance pureActualScalarCoefficientsAddGroup_rdb4876_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance pureActualScalarCoefficientsNonUnitalSemiring_rdb4876_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.pureActualScalarCoefficientsNonUnitalNonAssocSemiring
lemma adjoint_scalar_monomial_coeff (f:PowerSeries (Torus LaurentRay.vUnit Ω))
    (b m:M) (c:LaurentSeries ℚ) (n:ℕ) :
    coeff n (adjoint f (PowerSeries.C (Torus.monomial LaurentRay.vUnit Ω b c))) m=
      c*coeff n (adjoint f (PowerSeries.C (Torus.X LaurentRay.vUnit Ω b))) m := by
  rw [adjoint_torus_expansion]
  change (Finsupp.single b c).sum (fun d a=>a*coeff n (adjoint f (PowerSeries.C (Torus.X LaurentRay.vUnit Ω d))) m)=_
  exact Finsupp.sum_single_index (zero_mul _)

lemma hahnAction_monomial_coeff (f:PowerSeries (Torus LaurentRay.vUnit Ω))
    (b m:M) (c:LaurentSeries ℚ) (j:ℤ) :
    (hahnAction f (latticeHahn LaurentRay.vUnit Ω τ (Torus.monomial LaurentRay.vUnit Ω b c))).coeff j m=
      if 0≤j-τ b then c*coeff (j-τ b).toNat (adjoint f (PowerSeries.C (Torus.X LaurentRay.vUnit Ω b))) m else 0 := by
  rw [latticeHahn_monomial,hahnAction,hahn_single_shift_adjoint,
    HahnSeries.coeff_single_mul,one_mul,ofPowerSeries_coeff_int]
  split_ifs
  · exact adjoint_scalar_monomial_coeff Ω f b m c _
  · rfl

include hΩ in
lemma hahnAction_actual_coeff (f:PowerSeries (Torus LaurentRay.vUnit Ω))
    (F:Torus LaurentRay.vUnit Ω) (m:M) :
    (hahnAction f (latticeHahn LaurentRay.vUnit Ω τ F)).coeff (τ m) m=
      actualPolynomialAdjointCoefficient Ω τ f F m := by
  classical
  induction F using Finsupp.induction_linear with
  | zero=>simp [hahnAction_zero,actualPolynomialAdjointCoefficient]
  | add F G hF hG=>rw [map_add,hahnAction_add,HahnSeries.coeff_add,
      Finsupp.add_apply,actualPolynomialAdjointCoefficient_add,hF,hG]
  | single b c=>
    change (hahnAction f (latticeHahn LaurentRay.vUnit Ω τ (Torus.monomial LaurentRay.vUnit Ω b c))).coeff (τ m) m=
      actualPolynomialAdjointCoefficient Ω τ f (Torus.monomial LaurentRay.vUnit Ω b c) m
    rw [hahnAction_monomial_coeff,actualPolynomialAdjointCoefficient_monomial,
      actualMonomialAdjointCoefficient_read Ω hΩ τ,map_sub]
    split_ifs <;> simp

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_HalfspacePolynomialCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits HahnSeries
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.halfspacePolynomialCoefficientsCoeffRing
local instance halfspacePolynomialCoefficientsCoeffAddCommMonoid_rdb4876_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance halfspacePolynomialCoefficientsCoeffAddGroup_rdb4876_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance halfspacePolynomialCoefficientsCoeffNonUnitalSemiring_rdb4876_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
local instance halfspacePolynomialCoefficientsCoeffNonUnitalNonAssocSemiring_rdb4876_1 : NonUnitalNonAssocSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalNonAssocSemiring
include hΩ in
lemma actualPolynomialAdjointCoefficient_one (τ:M →+ ℤ) (F:Torus LaurentRay.vUnit Ω) (m:M) :
    actualPolynomialAdjointCoefficient Ω τ 1 F m=F m := by
  rw [←hahnAction_actual_coeff Ω hΩ,hahnAction_one,latticeHahn_coeff,ite_eq_left rfl]

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RootSectionHalfspace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint
open scoped BigOperators
open Classical
noncomputable section
variable {K M:Type*} [Field K] [AddCommGroup M]
variable (v:Kˣ) (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.targetCyclicRing
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.targetCyclicAddCommMonoid
local instance targetCyclicAddGroup_rdb4876_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
lemma torus_eval_finset_sum {J:Type*} (s:Finset J) (f:J → Torus v Ω) (m:M) :
    (∑j∈s,f j) m=∑j∈s,f j m := by
  induction s using Finset.induction_on with
  | empty=>rfl
  | @insert j s hj ih=>
    rw [Finset.sum_insert hj,Finset.sum_insert hj]
    change f j m+(∑j∈s,f j) m=_
    rw [ih]
include hΩ

lemma torus_target_cyclic (F G:Torus v Ω) (m:M)
    (h:∀r∈F.support,∀s∈G.support,r+s=m → Ω r m=0) : (F*G) m=(G*F) m := by
  change (Torus.multiply v Ω F G) m=(Torus.multiply v Ω G F) m
  simp only [Torus.multiply,Finsupp.sum,Finsupp.finsetSum_apply]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  by_cases he:r+s=m
  · have hrs:Ω r s=0 := by
      have H:=h r hr s hs he
      rw [←he,map_add,hΩ r,zero_add] at H
      exact H
    have hsr:Ω s r=0 := by rw [alternating_skew Ω hΩ,hrs,neg_zero]
    simp only [←he,Finsupp.single_eq_same,add_comm s r,hrs,hsr,zpow_zero,
      Units.val_one,mul_comm]
  · have he':s+r≠m:=by simpa only [add_comm s r] using he
    rw [Finsupp.single_eq_of_ne (Ne.symm he),Finsupp.single_eq_of_ne (Ne.symm he')]

lemma series_target_cyclic (F G:PowerSeries (Torus v Ω)) (N:ℕ) (m:M)
    (h:∀i j,i+j=N → ∀r∈(coeff i F).support,∀s∈(coeff j G).support,r+s=m → Ω r m=0) :
    coeff N (F*G) m=coeff N (G*F) m := by
  simp only [coeff_mul,torus_eval_finset_sum]
  rw [←Finset.Nat.sum_antidiagonal_swap (f:=fun p:ℕ×ℕ=>(coeff p.1 G*coeff p.2 F) m)]
  apply Finset.sum_congr rfl
  intro p hp
  exact torus_target_cyclic v Ω hΩ _ _ m (h p.1 p.2 (Finset.HasAntidiagonal.mem_antidiagonal.mp hp))

lemma adjoint_target_cyclic (F:PowerSeries (Torus v Ω)) (b m:M) (N:ℕ)
    (hF:constantCoeff F=1)
    (h:∀i j,i+j=N → ∀r∈(coeff i F).support,
       ∀s∈(coeff j (invOfUnit F 1)).support,r+(s+b)=m → Ω r m=0) :
    coeff N (adjoint F (PowerSeries.C (Torus.X v Ω b))) m=
      coeff N (PowerSeries.C (Torus.X v Ω b)) m := by
  rw [adjoint,mul_assoc]
  rw [series_target_cyclic v Ω hΩ F (PowerSeries.C (Torus.X v Ω b)*invOfUnit F 1) N m]
  · rw [mul_assoc,invOfUnit_mul F 1 hF,mul_one]
  · intro i j hij r hr s hs he
    have hs':coeff j (invOfUnit F 1) (s-b)≠0 := by
      have H:=Finsupp.mem_support_iff.mp hs
      rw [coeff_C_mul] at H
      have Hread:=X_mul_coeff v Ω (coeff j (invOfUnit F 1)) (s-b) b
      rw [sub_add_cancel] at Hread
      rw [Hread] at H
      exact (mul_ne_zero_iff.mp H).1
    exact h i j hij r hr (s-b) (Finsupp.mem_support_iff.mpr hs') (by simpa only [sub_add_cancel] using he)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RootCoefficientLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits
open scoped BigOperators
open Classical
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d)

include hcoord in
lemma root_interval_orthogonal (base m b r s:M) (d:I → ℕ)
    (hm:m=base+C (fun i=>(d i:ℤ)))
    (hb:∃k,HasRootDegree C k (b-base))
    (hr:∃k,HasRootDegree C k r) (hs:∃k,HasRootDegree C k s)
    (he:r+(s+b)=m) (ho:∀i,0<d i → Ω (simpleRoot C i) m=0) : Ω r m=0 := by
  obtain ⟨kb,hb⟩:=hb
  obtain ⟨kr,hr⟩:=hr
  obtain ⟨ks,hs⟩:=hs
  obtain ⟨ab,_,hcb,_⟩:=root_coordinates C coord hcoord hb
  obtain ⟨ar,_,hcr,_⟩:=root_coordinates C coord hcoord hr
  obtain ⟨as',_,hcs,_⟩:=root_coordinates C coord hcoord hs
  have hc:coord r+(coord s+coord (b-base))=(fun i=>(d i:ℤ)) := by
    rw [←map_add,←map_add]
    have he':r+(s+(b-base))=C (fun i=>(d i:ℤ)):=by rw [←add_sub_assoc,←add_sub_assoc,he,hm]; abel
    rw [he',hcoord]
  have hid:∀i,(ar i:ℤ)+(as' i:ℤ)+(ab i:ℤ)=(d i:ℤ):=by
    intro i
    have H:=congrFun hc i
    simp only [Pi.add_apply] at H
    rw [hcb,hcr,hcs] at H
    omega
  rw [root_simple_expansion C coord hcoord hr,map_sum]
  simp only [AddMonoidHom.finsetSum_apply,map_zsmul,AddMonoidHom.zsmul_apply,smul_eq_mul]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi:0<d i
  · rw [ho i hi,mul_zero]
  · have hai:ar i=0:=by have H:=hid i; omega
    rw [hcr,hai,Int.natCast_zero,zero_mul]

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.rootCoefficientLocalityRing
local instance rootCoefficientLocalityAddCommMonoid_rdb4876_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) :=
  (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance rootCoefficientLocalityAddGroup_rdb4876_1 : AddGroup (Torus LaurentRay.vUnit Ω) :=
  (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
include hΩ hcoord in
lemma actualMonomialAdjoint_locality (f:CompletedPositive LaurentRay.vUnit Ω C)
    (base m b:M) (d:I → ℕ) (hm:m=base+C (fun i=>(d i:ℤ)))
    (hb:∃k,HasRootDegree C k (b-base))
    (ho:∀i,0<d i → Ω (simpleRoot C i) m=0) :
    actualMonomialAdjointCoefficient Ω (rootOrder coord) f.val b m=
      actualMonomialAdjointCoefficient Ω (rootOrder coord) 1 b m := by
  have H:∀N,coeff N (adjoint f.val (PowerSeries.C (Torus.X LaurentRay.vUnit Ω b))) m=
      coeff N (PowerSeries.C (Torus.X LaurentRay.vUnit Ω b)) m := by
    intro N
    apply adjoint_target_cyclic LaurentRay.vUnit Ω hΩ f.val b m N f.property.1
    intro i j hij r hr s hs he
    apply root_interval_orthogonal Ω C coord hcoord base m b r s d hm hb
      ⟨i,chart_root_of_ne LaurentRay.vUnit Ω C f i r (Finsupp.mem_support_iff.mp hr)⟩
      ⟨j,?_⟩ he ho
    by_contra hh
    exact (Finsupp.mem_support_iff.mp hs) (SeriesGraded.inverse LaurentRay.vUnit Ω C f.property.2 j s hh)
  unfold actualMonomialAdjointCoefficient actualRootCoefficient
  split_ifs
  · have H1:=adjoint_monomial_coeff LaurentRay.vUnit Ω hΩ f.val b (m-b)
      ((rootOrder coord (m-b)).toNat)
    have H2:=adjoint_monomial_coeff LaurentRay.vUnit Ω hΩ 1 b (m-b)
      ((rootOrder coord (m-b)).toNat)
    rw [sub_add_cancel] at H1 H2
    rw [←H1,←H2,H]
    have hI:invOfUnit (1:PowerSeries (Torus LaurentRay.vUnit Ω)) 1=1 := by
      simpa only [mul_one] using (invOfUnit_mul (1:PowerSeries (Torus LaurentRay.vUnit Ω)) 1 (by simp))
    simp only [adjoint,hI,one_mul,mul_one]
  · rfl

include hΩ hcoord in
lemma actualPolynomialAdjoint_locality (f:CompletedPositive LaurentRay.vUnit Ω C)
    (base m:M) (d:I → ℕ) (hm:m=base+C (fun i=>(d i:ℤ)))
    (F:Torus LaurentRay.vUnit Ω)
    (hF:∀b∈F.support,∃k,HasRootDegree C k (b-base))
    (ho:∀i,0<d i → Ω (simpleRoot C i) m=0) :
    actualPolynomialAdjointCoefficient Ω (rootOrder coord) f.val F m=F m := by
  rw [←actualPolynomialAdjointCoefficient_one Ω hΩ (rootOrder coord) F m]
  unfold actualPolynomialAdjointCoefficient Finsupp.sum
  apply Finset.sum_congr rfl
  intro b hb
  change F b*actualMonomialAdjointCoefficient Ω (rootOrder coord) f.val b m=
    F b*actualMonomialAdjointCoefficient Ω (rootOrder coord) 1 b m
  exact congrArg (fun x=>F b*x) (actualMonomialAdjoint_locality Ω hΩ C coord hcoord f base m b d hm (hF b hb) ho)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_StationaryIntegerSequences
attribute [-simp] _root_.OAI.ElementaryPositivity.TriangularDynamics.extendedTotal_last _root_.OAI.ElementaryPositivity.TriangularDynamics.extendedTotal_succ _root_.OAI.ElementaryPositivity.TriangularDynamics.extendedTotal_zero _root_.OAI.ElementaryPositivity.TriangularDynamics.forwardCoord_roots _root_.OAI.ElementaryPositivity.TriangularDynamics.levelNode_last _root_.OAI.ElementaryPositivity.TriangularDynamics.levelNode_zero _root_.OAI.ElementaryPositivity.TriangularDynamics.omega_anchor_delta _root_.OAI.ElementaryPositivity.TriangularDynamics.omega_anchors _root_.OAI.ElementaryPositivity.TriangularDynamics.omega_delta_anchor _root_.OAI.ElementaryPositivity.TriangularDynamics.omega_delta_delta _root_.OAI.ElementaryPositivity.TriangularDynamics.partialBridge_cycle _root_.OAI.ElementaryPositivity.TriangularDynamics.partialBridge_nil _root_.OAI.ElementaryPositivity.TriangularDynamics.scheduledBridge_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics

lemma period_total_nonpos (B K : ℕ → ℤ) (hB : ∀ n, 0 ≤ B n)
    (hK : Monotone K) (step : ∀ n, B (n+1) = B n - K (n+1)) (n : ℕ) :
    K n ≤ 0 := by
  by_contra hn
  have hk : 1 ≤ K n := by omega
  have hb : ∀ t : ℕ, B (n+t) ≤ B n - (t:ℤ) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have hm := hK (show n ≤ n+t+1 by omega)
      have hs := step (n+t)
      simp only [Nat.add_succ, Nat.add_zero, Nat.cast_succ] at *
      omega
  have H := hb ((B n).toNat+1)
  have H0 := hB (n+((B n).toNat+1))
  have Hn := Int.toNat_of_nonneg (hB n)
  omega

lemma monotone_int_stabilizes (a : ℕ → ℤ) (ha : Monotone a)
    (hb : ∃ b, ∀ n, a n ≤ b) : ∃ N, ∀ n, N ≤ n → a n = a N := by
  obtain ⟨v,⟨N,hN⟩,hv⟩ := Int.exists_greatest_of_bdd
    (P := fun z => ∃ n, a n = z)
    (by obtain ⟨b,hb⟩ := hb; exact ⟨b,fun z ⟨n,hn⟩ => hn ▸ hb n⟩)
    ⟨a 0,0,rfl⟩
  refine ⟨N,fun n hn => le_antisymm ?_ (ha hn)⟩
  rw [hN]
  exact hv (a n) ⟨n,rfl⟩

lemma finite_coordinates_stabilize {ι : Type*} [Fintype ι]
    (a : ℕ → ι → ℤ) (ha : ∀ i, Monotone (fun n => a n i))
    (hs : ∀ n, ∑ i, a n i ≤ 0) :
    ∃ N, ∀ n, N ≤ n → ∀ i, a n i = a N i := by
  classical
  have hb : ∀ i, ∃ b, ∀ n, a n i ≤ b := by
    intro i
    refine ⟨-∑ j ∈ Finset.univ.erase i, a 0 j,fun n => ?_⟩
    have H := Finset.sum_le_sum (s := Finset.univ.erase i)
      (fun j _ => ha j (show 0 ≤ n by omega))
    have he := Finset.sum_erase_add (Finset.univ : Finset ι) (a n) (Finset.mem_univ i)
    have Hn := hs n
    dsimp only at H he
    omega
  choose N hN using fun i => monotone_int_stabilizes (fun n => a n i) (ha i) (hb i)
  refine ⟨Finset.univ.sup N,fun n hn i => ?_⟩
  have hi : N i ≤ Finset.univ.sup N := Finset.le_sup (f := N) (Finset.mem_univ i)
  rw [hN i n (hi.trans hn),hN i _ hi]

lemma nonnegative_affine_slope (a b : ℤ) (h : ∃ N : ℕ, ∀ L, N ≤ L →
    0 ≤ a + (L:ℤ)*b) : 0 ≤ b := by
  obtain ⟨N,hN⟩ := h
  by_contra hb
  have hb' : b ≤ -1 := by omega
  let L := max N (a.toNat+1)
  have hL := hN L (le_max_left _ _)
  have hLa : a < (L:ℤ) := by
    have hh : a.toNat+1 ≤ L := le_max_right _ _
    have ha : a ≤ (a.toNat:ℤ) := by omega
    omega
  have hL0 : (0:ℤ) ≤ L := Int.natCast_nonneg L
  nlinarith

lemma concave_nonpositive_zero (D : ℕ) (K : ℕ → ℤ)
    (h0 : K 0 = 0) (hD : K D = 0)
    (hn : ∀ i, i ≤ D → K i ≤ 0)
    (hc : ∀ i, 0 < i → i < D → 0 ≤ 2*K i-K (i-1)-K (i+1)) :
    ∀ i, i ≤ D → K i = 0 := by
  obtain ⟨j,hj,hmin⟩ := Finset.exists_min_image (Finset.range (D+1)) K
    (by exact ⟨0,by simp⟩)
  have hjD : j ≤ D := by
    have h := Finset.mem_range.mp hj
    omega
  have hm : ∀ i, i ≤ D → K j ≤ K i := by
    intro i hi
    exact hmin i (Finset.mem_range.mpr (by omega))
  have propagate : ∀ i, i ≤ D → K i = K j → K j = 0 := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro hi he
      by_cases hz : i = 0
      · simpa [hz,h0] using he.symm
      by_cases hd : i = D
      · simpa [hd,hD] using he.symm
      have H := hc i (by omega) (by omega)
      have Hl := hm (i-1) (by omega)
      have Hr := hm (i+1) (by omega)
      have he' : K (i-1) = K j := by omega
      exact ih (i-1) (by omega) (by omega) he'
  have hj0 := propagate j hjD rfl
  intro i hi
  have hh := hm i hi
  have hh' := hn i hi
  omega
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.TriangularDynamics
open ElementaryPositivity.QuantumTorus
variable {n : ℕ} {B : Type*} [Fintype B] [DecidableEq B]

omit [DecidableEq B] in
lemma total_levels (level : B → Fin n) (m : Lattice n B) :
    ∑ i, levelTotal level i m = ∑ b, m (Sum.inr b) := by
  simp only [levelTotal,AddMonoidHom.coe_mk,ZeroHom.coe_mk]
  rw [Finset.sum_comm]
  simp

variable (Ω : Lattice n B →+ Lattice n B →+ ℤ)

omit [Fintype B] in
lemma rotate_bridge_mono (level : B → Fin n) (L : ℕ) (m : Lattice n B) (b c : B) :
    m (Sum.inr c) ≤ rotate Ω level L m b (Sum.inr c) := by
  simp only [rotate,mutationIncomingLabel,Pi.add_apply,Pi.smul_apply,eventRoot_bridge,
    smul_eq_mul]
  split_ifs <;> simp

omit [Fintype B] in
lemma period_bridge_mono (level : B → Fin n) (cycle : List B) (L : ℕ) (m : Lattice n B) (c : B) :
    m (Sum.inr c) ≤ period Ω level cycle L m (Sum.inr c) := by
  induction cycle generalizing m with
  | nil => exact le_rfl
  | cons b bs ih =>
    exact (rotate_bridge_mono Ω level L m b c).trans (ih (rotate Ω level L m b))

lemma periodFunctional_rotate (level : B → Fin n) (i : Fin n) (L : ℕ) (m : Lattice n B) (b : B) :
    periodFunctional level i L (rotate Ω level L m b) = periodFunctional level i L m := by
  simp only [rotate,mutationIncomingLabel,map_add,map_zsmul,periodFunctional_eventRoot,
    smul_zero,add_zero]

lemma periodFunctional_period (level : B → Fin n) (i : Fin n) (cycle : List B)
    (L : ℕ) (m : Lattice n B) :
    periodFunctional level i L (period Ω level cycle L m) = periodFunctional level i L m := by
  induction cycle generalizing m with
  | nil => rfl
  | cons b bs ih =>
    change periodFunctional level i L (period Ω level bs L (rotate Ω level L m b)) = _
    rw [ih,periodFunctional_rotate]

omit [Fintype B] in
lemma history_bridge_mono (level : B → Fin n) (cycle : List B) (m : Lattice n B) (b : B) :
    Monotone (fun L => history Ω level cycle m L (Sum.inr b)) := by
  apply monotone_nat_of_le_succ
  intro L
  exact period_bridge_mono Ω level cycle L _ b

lemma history_total_mono (level : B → Fin n) (cycle : List B) (m : Lattice n B) (i : Fin n) :
    Monotone (fun L => levelTotal level i (history Ω level cycle m L)) := by
  intro L L' h
  apply Finset.sum_le_sum
  intro b _
  split_ifs
  · exact history_bridge_mono Ω level cycle m b h
  · rfl

lemma history_deficit_step (level : B → Fin n) (cycle : List B) (m : Lattice n B)
    (i : Fin n) (N L : ℕ) :
    cutDeficit level i N (L+1) (history Ω level cycle m (L+1)) =
      cutDeficit level i N L (history Ω level cycle m L) -
        levelTotal level i (history Ω level cycle m (L+1)) := by
  have h := periodFunctional_period Ω level i cycle L (history Ω level cycle m L)
  change periodFunctional level i L (history Ω level cycle m (L+1)) = _ at h
  simp only [cutDeficit,periodFunctional,AddMonoidHom.add_apply,AddMonoidHom.zsmul_apply,
    smul_eq_mul,Nat.cast_add,Nat.cast_one] at *
  linear_combination -h

lemma history_total_nonpos (level : B → Fin n) (cycle : List B) (m : Lattice n B)
    (N : ℕ) (hs : ∀ L i, 0 ≤ cutDeficit level i N L (history Ω level cycle m L))
    (L : ℕ) (i : Fin n) : levelTotal level i (history Ω level cycle m L) ≤ 0 :=
  period_total_nonpos (fun L => cutDeficit level i N L (history Ω level cycle m L))
    (fun L => levelTotal level i (history Ω level cycle m L)) (fun L => hs L i)
    (history_total_mono Ω level cycle m i) (history_deficit_step Ω level cycle m i N) L

lemma history_bridge_stabilizes (level : B → Fin n) (cycle : List B) (m : Lattice n B)
    (N : ℕ) (hs : ∀ L i, 0 ≤ cutDeficit level i N L (history Ω level cycle m L)) :
    ∃ T, ∀ L, T ≤ L → ∀ b, history Ω level cycle m L (Sum.inr b) =
      history Ω level cycle m T (Sum.inr b) := by
  apply finite_coordinates_stabilize (fun L b => history Ω level cycle m L (Sum.inr b))
    (history_bridge_mono Ω level cycle m)
  intro L
  rw [←total_levels level]
  exact Finset.sum_nonpos (fun i _ => history_total_nonpos Ω level cycle m N hs L i)
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularLateStationarity
attribute [-simp] _root_.OAI.ElementaryPositivity.TriangularDynamics.forwardCoord_roots _root_.OAI.ElementaryPositivity.TriangularDynamics.levelNode_last _root_.OAI.ElementaryPositivity.TriangularDynamics.levelNode_zero _root_.OAI.ElementaryPositivity.TriangularDynamics.omega_anchor_delta _root_.OAI.ElementaryPositivity.TriangularDynamics.omega_anchors _root_.OAI.ElementaryPositivity.TriangularDynamics.omega_delta_anchor _root_.OAI.ElementaryPositivity.TriangularDynamics.omega_delta_delta _root_.OAI.ElementaryPositivity.TriangularDynamics.partialBridge_cycle _root_.OAI.ElementaryPositivity.TriangularDynamics.partialBridge_nil _root_.OAI.ElementaryPositivity.TriangularDynamics.scheduledBridge_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open ElementaryPositivity.QuantumTorus
variable {n : ℕ} {B : Type*} [Fintype B] [DecidableEq B]
variable (Ω : Lattice n B →+ Lattice n B →+ ℤ)

omit [Fintype B] in
lemma period_of_bridge_eq (level : B → Fin n) (cycle : List B) (L : ℕ) (m : Lattice n B)
    (h : ∀ b, period Ω level cycle L m (Sum.inr b) = m (Sum.inr b)) :
    period Ω level cycle L m = m ∧ ∀ b ∈ cycle, 0 ≤ Ω (eventRoot level L b) m := by
  induction cycle generalizing m with
  | nil => exact ⟨rfl,by simp⟩
  | cons b bs ih =>
    have hle := period_bridge_mono Ω level bs L (rotate Ω level L m b) b
    change rotate Ω level L m b (Sum.inr b) ≤ period Ω level (b::bs) L m (Sum.inr b) at hle
    rw [h b] at hle
    have ht : max 0 (-Ω (eventRoot level L b) m) = 0 := by
      simp only [rotate,mutationIncomingLabel,Pi.add_apply,Pi.smul_apply,eventRoot_bridge,
        ite_true, if_true,smul_eq_mul,mul_one] at hle
      omega
    have hfix : rotate Ω level L m b = m := by
      simp only [rotate,mutationIncomingLabel,ht,zero_zsmul,add_zero]
    have hp : period Ω level (b::bs) L m = period Ω level bs L m := by
      change period Ω level bs L (rotate Ω level L m b) = _
      rw [hfix]
    have H := ih m (by intro c; simpa only [hp] using h c)
    refine ⟨hp.trans H.1,fun c hc => ?_⟩
    rcases List.mem_cons.mp hc with rfl | hc
    · omega
    · exact H.2 c hc

lemma history_late_fixed (level : B → Fin n) (cycle : List B) (m : Lattice n B)
    (N : ℕ) (hs : ∀ L i, 0 ≤ cutDeficit level i N L (history Ω level cycle m L)) :
    ∃ T, (∀ L, T ≤ L → history Ω level cycle m L = history Ω level cycle m T) ∧
      ∀ L, T ≤ L → ∀ b ∈ cycle, 0 ≤ Ω (eventRoot level L b) (history Ω level cycle m T) := by
  obtain ⟨T,hT⟩ := history_bridge_stabilizes Ω level cycle m N hs
  have he : ∀ L, T ≤ L → period Ω level cycle L (history Ω level cycle m L) =
      history Ω level cycle m L ∧
      ∀ b ∈ cycle, 0 ≤ Ω (eventRoot level L b) (history Ω level cycle m L) := by
    intro L hL
    apply period_of_bridge_eq
    intro b
    change history Ω level cycle m (L+1) (Sum.inr b) = history Ω level cycle m L (Sum.inr b)
    rw [hT (L+1) (by omega) b,hT L hL b]
  have hconst : ∀ k, history Ω level cycle m (T+k) = history Ω level cycle m T := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.add_succ,history]
      exact ((he (T+k) (by omega)).1).trans ih
  refine ⟨T,?_,?_⟩
  · intro L hL
    simpa only [Nat.add_sub_of_le hL] using hconst (L-T)
  · intro L hL b hb
    have HH := (he L hL).2 b hb
    have H := hconst (L-T)
    rw [Nat.add_sub_of_le hL] at H
    simpa only [H] using HH

omit [Fintype B] in
lemma eventRoot_pairing (level : B → Fin n) (L : ℕ) (b : B) (m : Lattice n B) :
    Ω (eventRoot level L b) m = Ω (eventRoot level 0 b) m + (L:ℤ)*Ω (delta level b) m := by
  simp only [eventRoot,Nat.cast_zero,zero_zsmul,add_zero,map_add,map_zsmul,
    AddMonoidHom.add_apply,AddMonoidHom.zsmul_apply,smul_eq_mul]

omit [Fintype B] in
lemma period_fixed (level : B → Fin n) (cycle : List B) (L : ℕ) (m : Lattice n B)
    (hp : ∀ b ∈ cycle, 0 ≤ Ω (eventRoot level L b) m) : period Ω level cycle L m = m := by
  induction cycle with
  | nil => rfl
  | cons b bs ih =>
    change period Ω level bs L (mutationIncomingLabel Ω (eventRoot level L b) m) = m
    rw [mutationIncomingLabel_nonnegative Ω _ m (hp b (by simp))]
    exact ih (by intro c hc; exact hp c (by simp [hc]))

omit [Fintype B] in
lemma period_injective (hΩ : ∀ m, Ω m m = 0) (level : B → Fin n) (cycle : List B) (L : ℕ) :
    Function.Injective (period Ω level cycle L) := by
  induction cycle with
  | nil => exact Function.injective_id
  | cons b bs ih =>
    intro m m' h
    apply (mutationIncomingLabelEquiv Ω (eventRoot level L b) (hΩ _)).injective
    apply ih
    exact h

omit [Fintype B] in
lemma history_injective (hΩ : ∀ m, Ω m m = 0) (level : B → Fin n) (cycle : List B) (L : ℕ) :
    Function.Injective (fun m => history Ω level cycle m L) := by
  induction L with
  | zero => exact Function.injective_id
  | succ L ih =>
    intro m m' h
    apply ih
    exact period_injective Ω hΩ level cycle L h

omit [Fintype B] in
lemma history_fixed (level : B → Fin n) (cycle : List B) (m : Lattice n B)
    (hp : ∀ L b, b ∈ cycle → 0 ≤ Ω (eventRoot level L b) m) (L : ℕ) :
    history Ω level cycle m L = m := by
  induction L with
  | zero => rfl
  | succ L ih =>
    rw [history,ih]
    exact period_fixed Ω level cycle L m (hp L)
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.TriangularDynamics
open ElementaryPositivity.QuantumTorus
variable {n : ℕ} {B : Type*} [Fintype B] [DecidableEq B]

omit [DecidableEq B] in
lemma extendedTotal_nonpos (level : B → Fin n) (m : Lattice n B)
    (h : ∀ i, levelTotal level i m ≤ 0) (k : ℕ) : extendedTotal level m k ≤ 0 := by
  unfold extendedTotal
  split_ifs with hk
  · exact h _
  · rfl

omit [DecidableEq B] in
lemma extendedTotal_all_zero (level : B → Fin n) (m : Lattice n B)
    (h : ∀ k, k ≤ n+1 → extendedTotal level m k = 0) (k : ℕ) :
    extendedTotal level m k = 0 := by
  by_cases hk : k ≤ n+1
  · exact h k hk
  · simp [extendedTotal,show ¬(0<k ∧ k≤n) by omega]

variable (Ω : Lattice n B →+ Lattice n B →+ ℤ)

lemma tropical_history_stationary (hΩ : ∀ m, Ω m m = 0)
    (level : B → Fin n) (hl : Function.Surjective level)
    (cycle : List B) (hcycle : ∀ b, b ∈ cycle)
    (hdelta : ∀ b m, Ω (delta level b) m =
      2*extendedTotal level m ((level b).val+1) - extendedTotal level m (level b).val -
        extendedTotal level m ((level b).val+2))
    (m : Lattice n B) (N : ℕ)
    (hs : ∀ L i, 0 ≤ cutDeficit level i N L (history Ω level cycle m L)) :
    (∀ i, levelTotal level i m = 0) ∧
      (∀ b, 0 ≤ Ω (eventRoot level 0 b) m) ∧
      (∀ L, history Ω level cycle m L = m) := by
  obtain ⟨T,hT,hp⟩ := history_late_fixed Ω level cycle m N hs
  let star := history Ω level cycle m T
  have hslope : ∀ b, 0 ≤ Ω (delta level b) star := by
    intro b
    apply nonnegative_affine_slope (Ω (eventRoot level 0 b) star)
    refine ⟨T,fun L hL => ?_⟩
    rw [←eventRoot_pairing]
    exact hp L hL b (hcycle b)
  have ht : ∀ k, k ≤ n+1 → extendedTotal level star k = 0 := by
    apply concave_nonpositive_zero (n+1) (extendedTotal level star)
      (extendedTotal_zero _ _) (extendedTotal_last _ _)
    · intro k _
      exact extendedTotal_nonpos level star (fun i => history_total_nonpos Ω level cycle m N hs T i) k
    · intro k hk hkn
      let i : Fin n := ⟨k-1,by omega⟩
      obtain ⟨b,hb⟩ := hl i
      have HH := hslope b
      rw [hdelta,hb] at HH
      have hi : i.val+1=k := by dsimp [i]; omega
      have hi' : i.val+2=k+1 := by omega
      rw [hi,hi'] at HH
      exact HH
  have hall := extendedTotal_all_zero level star ht
  have hd0 : ∀ b, Ω (delta level b) star = 0 := by
    intro b
    rw [hdelta,hall,hall,hall]
    ring
  have hp0 : ∀ b, 0 ≤ Ω (eventRoot level 0 b) star := by
    intro b
    have HH := hp T le_rfl b (hcycle b)
    change 0 ≤ Ω (eventRoot level T b) star at HH
    rw [eventRoot_pairing,hd0,mul_zero,add_zero] at HH
    exact HH
  have hpl : ∀ L b, b ∈ cycle → 0 ≤ Ω (eventRoot level L b) star := by
    intro L b _
    rw [eventRoot_pairing,hd0,mul_zero,add_zero]
    exact hp0 b
  have hm : m = star := by
    apply history_injective Ω hΩ level cycle T
    change history Ω level cycle m T = history Ω level cycle star T
    rw [history_fixed Ω level cycle star hpl T]
  refine ⟨?_,?_,?_⟩
  · intro i
    rw [hm,←extendedTotal_succ]
    exact hall _
  · simpa only [hm] using hp0
  · intro L
    rw [hm]
    exact history_fixed Ω level cycle star hpl L
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FiniteLatticePairing
attribute [-instance] _root_.OAI.ElementaryPositivity.TriangularDynamics.instAntisymmCellPhaseLE _root_.OAI.ElementaryPositivity.TriangularDynamics.instDecidableRelCellPhaseLE _root_.OAI.ElementaryPositivity.TriangularDynamics.instIsTransCellPhaseLE _root_.OAI.ElementaryPositivity.TriangularDynamics.instTotalCellPhaseLE
attribute [-simp] _root_.OAI.ElementaryPositivity.TriangularDynamics.forwardCoord_roots _root_.OAI.ElementaryPositivity.TriangularDynamics.levelNode_last _root_.OAI.ElementaryPositivity.TriangularDynamics.levelNode_zero _root_.OAI.ElementaryPositivity.TriangularDynamics.omega_anchor_delta _root_.OAI.ElementaryPositivity.TriangularDynamics.omega_anchors _root_.OAI.ElementaryPositivity.TriangularDynamics.omega_delta_anchor _root_.OAI.ElementaryPositivity.TriangularDynamics.omega_delta_delta _root_.OAI.ElementaryPositivity.TriangularDynamics.partialBridge_cycle _root_.OAI.ElementaryPositivity.TriangularDynamics.partialBridge_nil _root_.OAI.ElementaryPositivity.TriangularDynamics.scheduledBridge_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma matrixPairing_apply (K : Matrix V V ℤ) (x y : V → ℤ) :
    matrixPairing K x y = ∑ a, ∑ b, x a * K a b * y b :=
  Matrix.toBilin'_apply _ _ _

lemma matrixPairing_single_left (K : Matrix V V ℤ) (a : V) (m : V → ℤ) :
    matrixPairing K (Pi.single a 1) m = ∑ b, K a b * m b := by
  rw [matrixPairing_apply,Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

lemma matrixPairing_skew (K : Matrix V V ℤ) (hK : ∀ a b, K a b = -K b a)
    (x y : V → ℤ) : matrixPairing K x y = -matrixPairing K y x := by
  rw [matrixPairing_apply,matrixPairing_apply,Finset.sum_comm]
  simp only [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [hK b a]
  ring

lemma matrixPairing_self (K : Matrix V V ℤ) (hK : ∀ a b, K a b = -K b a)
    (m : V → ℤ) : matrixPairing K m m = 0 := by
  have := matrixPairing_skew K hK m m
  omega

variable {n : ℕ} {B : Type*} [Fintype B] [DecidableEq B]

omit [Fintype B] [DecidableEq B] in
lemma chartMatrix_skew (level : B → Fin n) (bb : B → B → ℤ)
    (hbb : ∀ b c, bb b c = -bb c b) (a c : Vertex n B) :
    chartMatrix level bb a c = -chartMatrix level bb c a := by
  cases a <;> cases c <;> simp only [chartMatrix]
  · rfl
  · ring
  · ring
  · apply hbb

lemma chartPairing_self (level : B → Fin n) (bb : B → B → ℤ)
    (hbb : ∀ b c, bb b c = -bb c b) (m : Lattice n B) :
    chartPairing level bb m m = 0 :=
  matrixPairing_self _ (chartMatrix_skew level bb hbb) m

omit [DecidableEq B] in
lemma total_as_sum (level : B → Fin n) (m : Lattice n B) (k : ℕ) :
    extendedTotal level m k = ∑ b, if (level b).val+1=k then m (.inr b) else 0 := by
  unfold extendedTotal
  split_ifs with hk
  · change (∑ b, if level b = ⟨k-1,by omega⟩ then m (.inr b) else 0) = _
    apply Finset.sum_congr rfl
    intro b _
    have hh : level b = (⟨k-1,by omega⟩ : Fin n) ↔ (level b).val+1=k := by
      constructor
      · intro h; have := congrArg Fin.val h; dsimp at this; omega
      · intro h; apply Fin.ext; dsimp; omega
    simp only [hh]
  · symm
    apply Finset.sum_eq_zero
    intro b _
    have hne : ¬(level b).val+1=k := by have := (level b).isLt; omega
    simp [hne]

lemma chartPairing_anchor (level : B → Fin n) (bb : B → B → ℤ)
    (a : Fin (n+1)) (m : Lattice n B) :
    chartPairing level bb (anchor a) m =
      extendedTotal level m a.val - extendedTotal level m (a.val+1) := by
  change matrixPairing (chartMatrix level bb) (Pi.single (.inl a) 1) m = _
  rw [matrixPairing_single_left,Fintype.sum_sum_type]
  simp only [chartMatrix,zero_mul,Finset.sum_const_zero,zero_add]
  rw [total_as_sum,total_as_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  have h1 : a = (level b).succ ↔ (level b).val+1=a.val := by
    rw [Fin.ext_iff]; simp only [Fin.val_succ]; omega
  have h2 : a = (level b).castSucc ↔ (level b).val+1=a.val+1 := by
    rw [Fin.ext_iff]; simp only [Fin.val_castSucc]; omega
  simp only [h1,h2]
  split_ifs <;> ring

lemma chartPairing_delta (level : B → Fin n) (bb : B → B → ℤ)
    (b : B) (m : Lattice n B) :
    chartPairing level bb (delta level b) m =
      2*extendedTotal level m ((level b).val+1) - extendedTotal level m (level b).val -
        extendedTotal level m ((level b).val+2) := by
  simp only [delta,map_sub,AddMonoidHom.sub_apply,chartPairing_anchor,
    Fin.val_succ,Fin.val_castSucc]
  ring

lemma chart_tropical_stationary (level : B → Fin n) (hl : Function.Surjective level)
    (bb : B → B → ℤ) (hbb : ∀ b c, bb b c = -bb c b)
    (cycle : List B) (hcycle : ∀ b, b ∈ cycle) (m : Lattice n B) (N : ℕ)
    (hs : ∀ L i, 0 ≤ cutDeficit level i N L
      (history (chartPairing level bb) level cycle m L)) :
    (∀ i, levelTotal level i m = 0) ∧
      (∀ b, 0 ≤ chartPairing level bb (eventRoot level 0 b) m) ∧
      (∀ L, history (chartPairing level bb) level cycle m L = m) :=
  tropical_history_stationary _ (chartPairing_self level bb hbb) level hl cycle hcycle
    (chartPairing_delta level bb) m N hs

end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.TriangularDynamics
open scoped BigOperators

lemma triangularBB_skew {n : ℕ} (b c : Cell n) : triangularBB b c= -triangularBB c b := by
  unfold triangularBB
  ring

lemma triangularOmega_self {n : ℕ} (m : Lattice n (Cell n)) : triangularOmega n m m=0 :=
  chartPairing_self _ _ triangularBB_skew m

end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularGapPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}

lemma gap_ext (g f:GapIndex n) (h1:g.1.val=f.1.val) (h2:g.2.val=f.2.val) : g=f := by
  cases g with | mk i g =>
    cases f with | mk j f =>
      have hij:i=j:=Fin.ext h1
      subst j
      have hgf:g=f:=Fin.ext h2
      subst f
      rfl

lemma gapValue_read (c:GapIndex n → ℤ) (g:GapIndex n) : gapValue c (g.1.val+1) g.2.val=c g := by
  rw [gapValue,Finset.sum_eq_single g]
  · simp
  · intro f _ hfg
    have hf:¬(f.1.val+1=g.1.val+1 ∧ f.2.val=g.2.val) := by
      intro h
      exact hfg (gap_ext f g (by omega) h.2)
    simp only [hf,ite_false, if_false]
  · simp

end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularGaps
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq
attribute [-simp] _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularGaps

namespace Recurrence

variable {n : ℕ} (R : Recurrence n)

lemma diagonal_all (j i : ℕ) (hj : 1 ≤ j) (hji : j ≤ i) :
    R.u j i = R.T j i + R.u (j + 1) (i + 1) := by
  by_cases hi : i ≤ n
  · exact R.diagonal j i hj hji hi
  · rw [R.u_out j i (by omega), R.T_out j i (by omega),
      R.u_out (j + 1) (i + 1) (by omega)]

lemma row_mono_add (j i k : ℕ) (hj : 1 ≤ j) (hji : j ≤ i) (hik : i + k ≤ n) :
    R.T j (i + k) ≤ R.T j i := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := R.row j (i + k) hj (by omega) (by omega)
    have h' := ih (by omega)
    have he : i + (k + 1) = i + k + 1 := by omega
    rw [he]
    omega

lemma row_le_start (j i : ℕ) (hj : 1 ≤ j) (hji : j ≤ i) (hi : i ≤ n) :
    R.T j i ≤ R.T j j := by
  simpa [Nat.add_sub_of_le hji] using
    R.row_mono_add j j (i - j) hj le_rfl (by omega)

lemma partial_total (i : ℕ) (hi : i ≤ n) :
    (∑ k ∈ Finset.range i, (R.T (k+1) (k+1) + R.xi (k+1) (k+1))) + R.u 1 i =
      if i = 0 then 0 else 1 := by
  induction i with
  | zero => simp [R.u_out 1 0 (by omega)]
  | succ i ih =>
    have hp := ih (by omega)
    have hs := R.start (i+1) (by omega) hi
    rw [Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel] at hs
    by_cases hiz : i = 0
    · subst i
      simpa [R.u_out 1 0 (by omega)] using hs
    · simp only [ite_eq_right hiz] at hp
      simp only [ite_eq_right (show i + 1 ≠ 1 by omega), zero_add] at hs
      simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false, if_false]
      omega

lemma total_le_one :
    (∑ k ∈ Finset.range n, (R.T (k+1) (k+1) + R.xi (k+1) (k+1))) ≤ 1 := by
  have h := R.partial_total n le_rfl
  split_ifs at h <;> omega

lemma unique_start (s : ℕ) (hs : 1 ≤ s) (hsn : s ≤ n) (hpos : 0 < R.T s s) :
    R.T s s = 1 ∧
    (∀ j, 1 ≤ j → j ≤ n → R.T j j = if j = s then 1 else 0) ∧
    (∀ j, 1 ≤ j → j ≤ n → R.xi j j = 0) := by
  have h := Finset.sum_le_one_iff.mp R.total_le_one
  have hsi : s - 1 ∈ Finset.range n := by simp; omega
  have hs1 : s - 1 + 1 = s := by omega
  have hsp : R.T (s-1+1) (s-1+1) + R.xi (s-1+1) (s-1+1) ≠ 0 := by
    rw [hs1]; omega
  have hone := (h (s-1) (s-1) hsi hsi hsp hsp).2
  rw [hs1] at hone
  have honeT : R.T s s = 1 := by omega
  have others : ∀ j, 1 ≤ j → j ≤ n → j ≠ s → R.T j j + R.xi j j = 0 := by
    intro j hj hjn hjs
    by_contra hn
    have hji : j - 1 ∈ Finset.range n := by simp; omega
    have hj1 : j - 1 + 1 = j := by omega
    have ho := (h (s-1) (j-1) hsi hji hsp (by simpa [hj1] using hn)).1
    omega
  refine ⟨honeT, ?_, ?_⟩
  · intro j hj hjn
    by_cases hjs : j = s
    · simpa [hjs] using honeT
    · have ho := others j hj hjn hjs
      simp only [ite_eq_right hjs]
      omega
  · intro j hj hjn
    by_cases hjs : j = s
    · subst j; omega
    · have ho := others j hj hjn hjs
      omega

lemma anchor_run (s : ℕ) (hs : 1 ≤ s) (hsn : s ≤ n) (hpos : 0 < R.T s s)
    (i : ℕ) (hi : i ≤ n) : R.u 1 i = if 0 < i ∧ i < s then 1 else 0 := by
  obtain ⟨_, ht, hx⟩ := R.unique_start s hs hsn hpos
  induction i with
  | zero => simp [R.u_out 1 0 (by omega)]
  | succ i ih =>
    have hp := ih (by omega)
    have hst := R.start (i+1) (by omega) hi
    rw [ht (i+1) (by omega) hi, hx (i+1) (by omega) hi] at hst
    simp only [Nat.add_sub_cancel, add_zero] at hst
    split_ifs at hp hst ⊢ <;> omega

lemma other_rows_zero (s : ℕ) (hs : 1 ≤ s) (hsn : s ≤ n)
    (hpos : 0 < R.T s s) (j i : ℕ) (hjs : j ≠ s) : R.T j i = 0 := by
  by_cases hv : 1 ≤ j ∧ j ≤ i ∧ i ≤ n
  · have h := R.row_le_start j i hv.1 hv.2.1 hv.2.2
    have h0 := (R.unique_start s hs hsn hpos).2.1 j hv.1 (by omega)
    rw [ite_eq_right hjs] at h0
    omega
  · exact R.T_out j i hv

lemma diagonal_sum (j i t : ℕ) (hj : 1 ≤ j) (hji : j ≤ i) :
    R.u j i = (∑ k ∈ Finset.range t, R.T (j+k) (i+k)) + R.u (j+t) (i+t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ]
    have hd := R.diagonal_all (j+t) (i+t) (by omega) (by omega)
    rw [hd] at ih
    simpa only [Nat.add_assoc] using ih

lemma u_one_row (s : ℕ) (hs : 1 ≤ s) (hsn : s ≤ n) (hpos : 0 < R.T s s)
    (j i : ℕ) (hj : 1 ≤ j) (hji : j ≤ i) :
    R.u j i = if j ≤ s then R.T s (i+s-j) else 0 := by
  have hsum := R.diagonal_sum j i (n+1) hj hji
  rw [R.u_out (j+(n+1)) (i+(n+1)) (by omega), add_zero] at hsum
  rw [hsum]
  by_cases hjs : j ≤ s
  · rw [ite_eq_left hjs]
    rw [Finset.sum_eq_single (s-j)]
    · congr 1 <;> omega
    · intro k hk hks
      exact R.other_rows_zero s hs hsn hpos (j+k) (i+k) (by omega)
    · intro hk
      simp only [Finset.mem_range] at hk
      omega
  · rw [ite_eq_right hjs]
    apply Finset.sum_eq_zero
    intro k hk
    exact R.other_rows_zero s hs hsn hpos (j+k) (i+k) (by omega)

lemma row_formula (s : ℕ) (hs : 1 ≤ s) (hsn : s ≤ n) (hpos : 0 < R.T s s)
    (i : ℕ) (hsi : s ≤ i) (hi : i ≤ n) :
    R.T s i = if i + 1 < 2*s then 1 else 0 := by
  have hd := R.u_one_row s hs hsn hpos 1 (i+1-s) (by omega) (by omega)
  rw [ite_eq_left hs] at hd
  have he : i+1-s+s-1 = i := by omega
  rw [he] at hd
  rw [← hd, R.anchor_run s hs hsn hpos (i+1-s) (by omega)]
  split_ifs <;> omega

lemma xi_zero_before (s : ℕ) (hs : 1 ≤ s) (hsn : s ≤ n) (hpos : 0 < R.T s s)
    (j i : ℕ) (hj : 1 ≤ j) (hji : j ≤ i) (hi : i ≤ n) (hbefore : i+1 < 2*s) :
    R.xi j i = 0 := by
  by_cases hji' : j = i
  · subst i
    exact (R.unique_start s hs hsn hpos).2.2 j hj hi
  · have hr := R.row j (i-1) hj (by omega) (by omega)
    have he : i-1+1 = i := by omega
    rw [he] at hr
    by_cases hjs : j = s
    · subst j
      rw [R.row_formula s hs hsn hpos i hji hi,
        R.row_formula s hs hsn hpos (i-1) (by omega) (by omega),
        ite_eq_left hbefore, ite_eq_left (by omega)] at hr
      omega
    · rw [R.other_rows_zero s hs hsn hpos j i hjs,
        R.other_rows_zero s hs hsn hpos j (i-1) hjs] at hr
      omega

theorem positive_gap_zero_pairings (j i : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (hi : i ≤ n) (hu : 0 < R.u j i) :
    ∀ k, 1 ≤ k → k ≤ i → R.xi k i = 0 := by
  have hsum := R.diagonal_sum j i (n+1) hj hji
  rw [R.u_out (j+(n+1)) (i+(n+1)) (by omega), add_zero] at hsum
  have hp : 0 < ∑ k ∈ Finset.range (n+1), R.T (j+k) (i+k) := by omega
  obtain ⟨k, hk, htk⟩ := (Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp hp
  have hv : 1 ≤ j+k ∧ j+k ≤ i+k ∧ i+k ≤ n := by
    by_contra hn
    rw [R.T_out (j+k) (i+k) hn] at htk
    omega
  let s := j+k
  have hs : 1 ≤ s := hv.1
  have hsn : s ≤ n := by dsimp [s]; omega
  have hpos : 0 < R.T s s := by
    have hl := R.row_le_start (j+k) (i+k) hv.1 hv.2.1 hv.2.2
    dsimp [s]; omega
  have hur := R.u_one_row s hs hsn hpos j i hj hji
  have hjs : j ≤ s := by dsimp [s]; omega
  rw [ite_eq_left hjs] at hur
  have htarget : i+s-j ≤ n := by
    by_contra hn
    rw [R.T_out s (i+s-j) (by omega)] at hur
    omega
  have hf := R.row_formula s hs hsn hpos (i+s-j) (by omega) htarget
  have hbefore : i+1 < 2*s := by
    rw [hur] at hu
    split_ifs at hf <;> omega
  intro k hk hki
  exact R.xi_zero_before s hs hsn hpos k i hk hki hi hbefore

end Recurrence

namespace IntegerGaps
variable {n : ℕ} (A : IntegerGaps n)

 theorem positive_gap_zero_pairings (j i : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (hi : i ≤ n) (hu : 0 < A.u j i) :
    ∀ k, 1 ≤ k → k ≤ i → A.xi k i = 0 := by
  have hpos : 0 < A.recurrence.u j i := by
    change 0 < (A.u j i).toNat
    omega
  have h := A.recurrence.positive_gap_zero_pairings j i hj hji hi hpos
  intro k hk hki
  have hz := h k hk hki
  change (A.xi k i).toNat = 0 at hz
  have hn := A.xi_nonneg k i hk hki hi
  omega

end IntegerGaps
end ElementaryPositivity.TriangularGaps

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularGapOrthogonality
attribute [-simp] _root_.OAI.ElementaryPositivity.TriangularDynamics.levelNode_last _root_.OAI.ElementaryPositivity.TriangularDynamics.levelNode_zero _root_.OAI.ElementaryPositivity.TriangularDynamics.partialBridge_cycle _root_.OAI.ElementaryPositivity.TriangularDynamics.partialBridge_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}

lemma stationary_anchor_pair_zero (m:Lattice n (Cell n)) (hK:∀i,levelTotal cellLevel i m=0)
    (a:Fin (n+1)) : triangularOmega n (anchor a) m=0 := by
  have HT:∀i,extendedTotal cellLevel m i=0 := by
    intro i
    unfold extendedTotal
    split_ifs <;> first | exact hK _ | rfl
  change chartPairing cellLevel triangularBB (anchor a) m=0
  rw [chartPairing_anchor,HT,HT,sub_self]

lemma gapXi_cell (m:Lattice n (Cell n)) (b:Cell n) :
    gapXi m (b.2.val+1) (b.1.val+1)=triangularOmega n (eventRoot cellLevel 0 b) m := by
  have hb:=b.2.isLt
  rw [gapXi,dite_eq_left (by have hn:=b.1.isLt; omega)]
  congr 2

lemma gap_positive_u (c:GapIndex n → ℤ) (m:Lattice n (Cell n))
    (hm:m=anchor 0+forwardRoots c) (hK:∀i,levelTotal cellLevel i m=0)
    (g:GapIndex n) (hg:0 < c g) :
    ∃j,1 ≤ j ∧ j ≤ g.1.val+1 ∧ 0 < gapU c j (g.1.val+1) := by
  have ht:=g.2.isLt
  by_cases hz:g.2.val=0
  · refine ⟨1,by omega,by omega,?_⟩
    rw [gapU_first,←gapValue_end_eq c m hm hK,←hz,gapValue_read]
    exact hg
  · let j:=g.1.val+2-g.2.val
    have hj:1 ≤ j ∧ j ≤ g.1.val+1 ∧ g.1.val+1 ≤ n := by
      have hn:=g.1.isLt
      dsimp [j]
      omega
    refine ⟨j,hj.1,hj.2.1,?_⟩
    rw [gapU,ite_eq_left hj]
    have he:g.1.val+1+1-j=g.2.val:=by dsimp [j]; omega
    rw [he,gapValue_read]
    exact hg

lemma positive_level_event_zero (c:GapIndex n → ℤ) (m:Lattice n (Cell n))
    (hc:∀g,0 ≤ c g) (hm:m=anchor 0+forwardRoots c) (hK:∀i,levelTotal cellLevel i m=0)
    (hxi:∀b,0 ≤ triangularOmega n (eventRoot cellLevel 0 b) m)
    (g:GapIndex n) (hg:0 < c g) (b:Cell n) (hbg:b.1=g.1) :
    triangularOmega n (eventRoot cellLevel 0 b) m=0 := by
  obtain ⟨j,hj,hji,hu⟩:=gap_positive_u c m hm hK g hg
  let A:=actualIntegerGaps c m hc hm hK hxi
  have H:=A.positive_gap_zero_pairings j (g.1.val+1) hj hji (by have := g.1.isLt; omega) hu
    (b.2.val+1) (by omega) (by have hb:=b.2.isLt; have he:=congrArg Fin.val hbg; omega)
  change gapXi m (b.2.val+1) (g.1.val+1)=0 at H
  rw [←hbg,gapXi_cell] at H
  exact H

lemma positive_gap_target_zero (c:GapIndex n → ℤ) (m:Lattice n (Cell n))
    (hc:∀g,0 ≤ c g) (hm:m=anchor 0+forwardRoots c) (hK:∀i,levelTotal cellLevel i m=0)
    (hxi:∀b,0 ≤ triangularOmega n (eventRoot cellLevel 0 b) m)
    (g:GapIndex n) (hg:0 < c g) : triangularOmega n (forwardGap g) m=0 := by
  have HB:∀b:Cell n,b.1=g.1 → triangularOmega n (bridge b) m=0 := by
    intro b hb
    have H:=positive_level_event_zero c m hc hm hK hxi g hg b hb
    simp only [eventRoot,Nat.cast_zero,zero_smul,add_zero,map_sub,AddMonoidHom.sub_apply,
      stationary_anchor_pair_zero m hK,sub_zero] at H
    exact H
  have HN:∀t:Fin (g.1.val+3),triangularOmega n (Pi.single (levelNode g.1 t) 1) m=0 := by
    intro t
    unfold levelNode
    split_ifs
    · exact stationary_anchor_pair_zero m hK _
    · exact stationary_anchor_pair_zero m hK _
    · exact HB _ rfl
  rw [forwardGap,map_sub,AddMonoidHom.sub_apply,HN,HN,sub_self]
end
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.TriangularDynamics
open Classical
noncomputable section
variable {n : ℕ}

lemma phaseCycle_nodup : (phaseCycle n).Nodup := Finset.sort_nodup _ _
lemma phaseCycle_pairwise : (phaseCycle n).Pairwise phaseLE := by
  exact Finset.pairwise_sort _ _

end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularLevelQueues
attribute [-simp] _root_.OAI.ElementaryPositivity.TriangularDynamics.levelNode_last _root_.OAI.ElementaryPositivity.TriangularDynamics.levelNode_zero _root_.OAI.ElementaryPositivity.TriangularDynamics.partialBridge_cycle _root_.OAI.ElementaryPositivity.TriangularDynamics.partialBridge_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open Classical
noncomputable section
variable {n : ℕ}

lemma initialLevelQueue_mem (i : Fin n) (b : Cell n) :
    b∈initialLevelQueue i ↔ b.1=i := by
  rw [initialLevelQueue,List.mem_ofFn]
  constructor
  · rintro ⟨j,rfl⟩; rfl
  · intro hb
    cases b with | mk l r =>
      dsimp only at hb
      subst l
      exact ⟨r.rev,by simp⟩

lemma initialLevelQueue_nodup (i : Fin n) : (initialLevelQueue i).Nodup := by
  rw [initialLevelQueue,List.nodup_ofFn]
  intro j k h
  have hh:=congrArg cellRow h
  apply Fin.rev_injective
  exact Fin.ext hh

lemma initialLevelQueue_pairwise (i : Fin n) : (initialLevelQueue i).Pairwise phaseLE := by
  rw [initialLevelQueue,List.pairwise_ofFn]
  intro j k hjk
  apply Or.inl
  apply Or.inl
  change k.rev.val < j.rev.val
  simp only [Fin.val_rev]
  have := k.isLt
  omega

lemma phaseCycle_levelQueue (i : Fin n) : levelQueue (phaseCycle n) i=initialLevelQueue i := by
  apply List.Perm.eq_of_pairwise (fun a b _ _ hab hba=>Std.Antisymm.antisymm (r:=phaseLE) a b hab hba)
  · exact List.Pairwise.filter _ phaseCycle_pairwise
  · exact initialLevelQueue_pairwise i
  · apply (List.perm_ext_iff_of_nodup (List.Nodup.filter _ phaseCycle_nodup)
      (initialLevelQueue_nodup i)).mpr
    intro b
    simp only [List.mem_filter,decide_eq_true_eq,mem_phaseCycle,true_and,initialLevelQueue_mem]

end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_ForwardChartMutation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.ForwardChain
variable {M : Type*} [AddCommGroup M]
lemma gaps_ofFn_nodes {k:ℕ} (x:Fin (k+2) → M) :
    gaps (x 0) (List.ofFn (fun j:Fin k=>x j.succ.castSucc)) (x (Fin.last (k+1)))=
      List.ofFn (fun j:Fin (k+1)=>x j.succ-x j.castSucc) := by
  induction k with
  | zero => simp [gaps,List.ofFn_succ]
  | succ k ih =>
    rw [List.ofFn_succ,gaps,List.ofFn_succ]
    congr 1
    exact ih (fun j=>x j.succ)
end ElementaryPositivity.ForwardChain

end
section
namespace ElementaryPositivity.TriangularDynamics
open Classical
noncomputable section
variable {n : ℕ} {R : Type*} [CommRing R]

lemma levelNode_middle (i:Fin n) (j:Fin (i.val+1)) :
    levelNode i j.succ.castSucc=.inr ⟨i,j.rev⟩ := by
  simp only [levelNode,Fin.val_castSucc,Fin.val_succ]
  rw [dite_eq_right (by omega),dite_eq_right (by have := j.isLt; omega)]
  congr 2

lemma mem_gapIndices (g:GapIndex n) : g∈gapIndices n := by
  rcases g with ⟨i,j⟩
  exact List.mem_flatMap.mpr ⟨i,List.mem_finRange _,List.mem_map.mpr ⟨j,List.mem_finRange _,rfl⟩⟩
lemma gapIndices_nodup : (gapIndices n).Nodup := by
  rw [gapIndices,List.nodup_flatMap]
  constructor
  · intro i _
    exact (List.nodup_finRange _).map (fun a b h=>by cases h; rfl)
  · apply (List.nodup_finRange n).pairwise_of_forall_ne
    intro i j _ _ hij g hg hg'
    obtain ⟨a,_,ha⟩:=List.mem_map.mp hg
    obtain ⟨b,_,hb⟩:=List.mem_map.mp hg'
    exact hij (by simpa using congrArg Sigma.fst (ha.trans hb.symm))

lemma initial_levelGaps (i:Fin n) :
    levelGaps (anchor (n:=n)) bridge (phaseCycle n) i=
      (List.finRange (i.val+2)).map (fun j=>forwardGap (R:=ℤ) ⟨i,j⟩) := by
  rw [levelGaps,phaseCycle_levelQueue,initialLevelQueue,List.map_ofFn]
  have H:=ForwardChain.gaps_ofFn_nodes (fun j:Fin (i.val+3)=>
    (Pi.single (levelNode i j) 1:Vertex n (Cell n) → ℤ))
  simpa only [levelNode_zero,levelNode_last,levelNode_middle,anchor,bridge,
    forwardGap,List.ofFn_eq_map,Function.comp_def] using H

lemma initial_forwardInventory :
    forwardInventory anchor bridge (phaseCycle n)=
      (gapIndices n).map (forwardGap (R:=ℤ)) := by
  rw [forwardInventory,gapIndices,List.map_flatMap]
  congr 1
  funext i
  rw [initial_levelGaps,List.map_map]
  rfl

end
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.LatticeExtension
open scoped BigOperators
variable {V : Type*} [Fintype V]

variable (Ω : (V → ℤ) →+ (V → ℤ) →+ ℤ)

lemma form_self (hΩ : ∀m,Ω m m=0) (x : Extended V) : form Ω x x=0 := by
  rw [form_apply,hΩ,zero_add]
  have H : dot x.2 x.1=dot x.1 x.2 := by
    simp only [dot_apply]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [H,sub_self]

lemma form_nondegenerate [DecidableEq V] : ∀r≠0,∃m,form Ω r m≠0 := by
  intro r hr
  by_contra hh
  push Not at hh
  have hfirst : r.1=0 := by
    ext i
    have H:=hh (0,Pi.single i 1)
    simp only [form_apply,map_zero,dot_single,zero_add,zero_sub,neg_eq_zero] at H
    exact H
  have hsecond : r.2=0 := by
    ext i
    have H:=hh (Pi.single i 1,0)
    simp only [form_apply,hfirst,map_zero,AddMonoidHom.zero_apply,zero_add,
      dot_single,sub_zero] at H
    exact H
  exact hr (Prod.ext hfirst hsecond)
end ElementaryPositivity.LatticeExtension

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_PolynomialSection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ))

local instance polynomialSectionRing_rdb4876_1 : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance polynomialSectionAddCommMonoid_rdb4876_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance polynomialSectionAddGroup_rdb4876_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
omit [DecidableEq I] in
include hΩ in
lemma actualMonomialAdjoint_support (τ:M →+ ℤ) (f:CompletedPositive LaurentRay.vUnit Ω C)
    (b m:M) (hm:actualMonomialAdjointCoefficient Ω τ f.val b m≠0) :
    ∃d,HasRootDegree C d (m-b) := by
  have H:=normalizedMonomialAction_graded LaurentRay.vUnit Ω hΩ C f b
  unfold actualMonomialAdjointCoefficient actualRootCoefficient at hm
  split_ifs at hm with ht
  · refine ⟨(τ (m-b)).toNat,?_⟩
    by_contra hn
    exact hm (by rw [H _ _ hn,zero_mul])
  · exact (hm (zero_mul _)).elim

omit [DecidableEq I] in
include hΩ in
lemma actualPolynomialAdjoint_support (τ:M →+ ℤ) (f:CompletedPositive LaurentRay.vUnit Ω C)
    (F:Torus LaurentRay.vUnit Ω) (m:M)
    (hm:actualPolynomialAdjointCoefficient Ω τ f.val F m≠0) :
    ∃b∈F.support,∃d,HasRootDegree C d (m-b) := by
  classical
  unfold actualPolynomialAdjointCoefficient Finsupp.sum at hm
  obtain ⟨b,hb,hb'⟩:=Finset.exists_ne_zero_of_sum_ne_zero hm
  refine ⟨b,hb,actualMonomialAdjoint_support Ω hΩ C τ f b m ?_⟩
  intro hh
  exact hb' (show F b * actualMonomialAdjointCoefficient Ω τ f.val b m = 0 from by simp only [hh,mul_zero])

include hΩ in
lemma polynomialSection_support (h:M →+ ℝ) (F:Torus LaurentRay.vUnit Ω) (m:M)
    (hm:polynomialSectionCoefficient Ω C coord h F m≠0) :
    ∃b∈F.support,∃d,HasRootDegree C d (m-b) :=
  actualPolynomialAdjoint_support Ω hΩ C (rootOrder coord) (rootSectionChart Ω C h) F m hm

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RealLatticeRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LatticeRealization
open scoped BigOperators
open TriangularDynamics
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
lemma cast_injective : Function.Injective (cast (V:=V)) := by
  intro a b h
  ext i
  have H := congrFun h i
  change (a i : ℝ)=(b i : ℝ) at H
  exact_mod_cast H

variable (A : Matrix V V ℤ)

lemma realPairing_apply (x y : V → ℝ) :
    realPairing A x y=∑i,∑j,x i*(A i j:ℝ)*y j := Matrix.toBilin'_apply _ _ _

lemma realPairing_cast (x y : V → ℤ) :
    realPairing A (cast x) (cast y)=(matrixPairing A x y:ℝ) := by
  simp only [realPairing_apply,matrixPairing_apply,cast_apply,Int.cast_sum,Int.cast_mul]

lemma realPairing_skew (hA : ∀i j,A i j= -A j i) (x y : V → ℝ) :
    realPairing A x y= -realPairing A y x := by
  rw [realPairing_apply,realPairing_apply,Finset.sum_comm]
  simp only [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hA j i,Int.cast_neg]
  ring

lemma realPairing_self (hA : ∀i j,A i j= -A j i) (x : V → ℝ) :
    realPairing A x x=0 := by
  have H:=realPairing_skew A hA x x
  linarith

lemma realDot_apply (x y : V → ℝ) : realDot x y=∑i,x i*y i := by
  simp [realDot,Matrix.toBilin'_apply,Matrix.one_apply]
lemma realDot_comm (x y : V → ℝ) : realDot x y=realDot y x := by
  simp only [realDot_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring
lemma realDot_cast (x y : V → ℤ) :
    realDot (cast x) (cast y)=(LatticeExtension.dot x y:ℝ) := by
  simp only [realDot_apply,LatticeExtension.dot_apply,cast_apply,Int.cast_sum,Int.cast_mul]

omit [Fintype V] [DecidableEq V] in
lemma extendedCast_apply (x : LatticeExtension.Extended V) :
    extendedCast x=(cast x.1,cast x.2) := rfl
omit [Fintype V] [DecidableEq V] in
lemma extendedCast_injective : Function.Injective (extendedCast (V:=V)) := by
  intro a b h
  apply Prod.ext
  · exact cast_injective (congrArg Prod.fst h)
  · exact cast_injective (congrArg Prod.snd h)

lemma extendedRealForm_apply (x y : (V → ℝ) × (V → ℝ)) :
    extendedRealForm A x y=realPairing A x.1 y.1+realDot x.2 y.1-realDot x.1 y.2 := rfl

lemma extendedRealForm_self (hA : ∀i j,A i j= -A j i) (x : (V → ℝ) × (V → ℝ)) :
    extendedRealForm A x x=0 := by
  rw [extendedRealForm_apply,realPairing_self A hA,zero_add,realDot_comm x.2 x.1,sub_self]

lemma extendedRealForm_cast (x y : LatticeExtension.Extended V) :
    extendedRealForm A (extendedCast x) (extendedCast y)=
      (LatticeExtension.form (matrixPairing A) x y:ℝ) := by
  simp only [extendedRealForm_apply,extendedCast_apply,realPairing_cast,realDot_cast,
    LatticeExtension.form_apply,Int.cast_sub,Int.cast_add]

end ElementaryPositivity.LatticeRealization

end
section
namespace ElementaryPositivity.ForwardChain
variable {M M':Type*} [AddCommGroup M] [AddCommGroup M']
lemma gaps_map (a:M →+ M') (x y:M) (bs:List M) :
    gaps (a x) (bs.map a) (a y)=(gaps x bs y).map a := by
  induction bs generalizing x with
  | nil => simp [gaps,map_sub]
  | cons b bs ih => simp only [gaps,List.map_cons,map_sub,ih]
end ElementaryPositivity.ForwardChain

namespace ElementaryPositivity.TriangularDynamics
variable {n:ℕ} {M M':Type*} [AddCommGroup M] [AddCommGroup M']
lemma forwardInventory_map (a:M →+ M') (d:Fin (n+1) → M) (w:Cell n → M) (q:List (Cell n)) :
    forwardInventory (a ∘ d) (a ∘ w) q=(forwardInventory d w q).map a := by
  unfold forwardInventory
  rw [List.map_flatMap]
  congr 1
  funext i
  simp only [levelGaps,Function.comp_apply,←List.map_map,ForwardChain.gaps_map]
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus LatticeExtension LatticeRealization
open Classical
noncomputable section
variable {n:ℕ}

lemma initialFreeChart_inventory :
    ((gapIndices n).map (simpleRoot (initialFreeChart n).roots)).Perm
      (forwardInventory (includeVertices ∘ anchor) (includeVertices ∘ bridge) (phaseCycle n)) := by
  apply List.Perm.of_eq
  rw [forwardInventory_map,initial_forwardInventory,List.map_map]
  apply List.map_congr_left
  intro g _
  exact extendedRoot_eq g

lemma extendedOmega_self : ∀m,extendedOmega n m m=0 := form_self _ triangularOmega_self
lemma extendedOmega_nondegenerate : ∀r≠0,∃m,extendedOmega n r m≠0 := form_nondegenerate _
lemma triangularRealForm_self : ∀m, triangularRealForm n m m=0 :=
  extendedRealForm_self _ (chartMatrix_skew cellLevel triangularBB triangularBB_skew)
lemma triangularRealForm_compatible (m m':Extended (Vertex n (Cell n))) :
    triangularRealForm n (extendedCast m) (extendedCast m')=(extendedOmega n m m':ℝ) :=
  extendedRealForm_cast _ _ _
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularPolynomialStationarity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension LatticeRealization
open Classical
noncomputable section
variable {n:ℕ}

lemma cellLevel_surjective : Function.Surjective (@cellLevel n) := by
  intro i
  exact ⟨⟨i,⟨0,by omega⟩⟩,rfl⟩

lemma triangularExpression_stationary {N:ℕ} (f:ElementaryExpr N) (m:Lattice n (Cell n))
    (hm:triangularIncoming f m≠0) :
    (∀i,levelTotal cellLevel i m=0) ∧
      (∀b,0≤triangularOmega n (eventRoot cellLevel 0 b) m) ∧
      (∀L,history (triangularOmega n) cellLevel (phaseCycle n) m L=m) := by
  apply chart_tropical_stationary cellLevel cellLevel_surjective triangularBB triangularBB_skew
    (phaseCycle n) (mem_phaseCycle (n:=n)) m N
  intro L i
  have hzero : periodBridge (n:=n) 0 = bridge := by
    funext c
    simp [periodBridge]
  have hinv : ((gapIndices n).map (simpleRoot (initialFreeChart n).roots)).Perm
      (forwardInventory (includeVertices ∘ anchor) (includeVertices ∘ periodBridge 0) (phaseCycle n)) := by
    simpa only [hzero] using initialFreeChart_inventory (n:=n)
  have hm' : polynomialSectionIncoming (extendedOmega n) (initialFreeChart n).roots (initialFreeChart n).coord
      (f.eval LaurentRay.vUnit (extendedOmega n)
        (vertexDisplay (includeVertices ∘ anchor) (includeVertices ∘ periodBridge 0)))
      (includeVertices m)≠0 := by
    simpa only [triangularIncoming,triangularExpression,initialFreeChart,hzero] using hm
  exact genuine_history_cut_deficit (extendedOmega n) extendedOmega_self extendedCast extendedCast_injective
    (triangularRealForm n) triangularRealForm_self triangularRealForm_compatible extendedOmega_nondegenerate
    includeVertices extendedOmega_original (AddMonoidHom.fst _ _) (fun _=>rfl)
    (gapIndices n) (gapIndices_nodup (n:=n)) (mem_gapIndices (n:=n)) (initialFreeChart n) hinv f m hm' L i
end
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.TriangularDynamics
open scoped BigOperators
open QuantumTorus
open Classical
noncomputable section
variable {n:ℕ} {R:Type*} [CommRing R]

lemma forwardRoots_single (g:GapIndex n) (r:R) :
    forwardRoots (Pi.single g r)=r • forwardGap g := by
  rw [forwardRoots_apply,Finset.sum_eq_single g]
  · simp
  · intro h _ hh
    simp [Ne.symm hh]
  · simp

lemma forwardRoots_coord_gap (g:GapIndex n) :
    forwardRoots (forwardCoord (forwardGap (R:=R) g))=forwardGap g := by
  rw [forwardCoord_gap,forwardRoots_single,one_smul]

lemma forwardRoots_coord_level (i:Fin n)
    (h:forwardRoots (forwardCoord (Pi.single (.inl i.castSucc) (1:R)))=
      Pi.single (.inl i.castSucc) 1-Pi.single (.inl (0:Fin (n+1))) 1)
    (j:Fin (i.val+3)) :
    forwardRoots (forwardCoord (Pi.single (levelNode i j) (1:R)))=
      Pi.single (levelNode i j) 1-Pi.single (.inl (0:Fin (n+1))) 1 := by
  induction j using Fin.induction with
  | zero => simpa only [levelNode_zero] using h
  | succ j ih =>
    have H:=forwardRoots_coord_gap (R:=R) (⟨i,j⟩:GapIndex n)
    simp only [forwardGap,map_sub] at H
    rw [ih] at H
    exact sub_eq_iff_eq_add.mp H |>.trans (by abel)

lemma forwardRoots_coord_anchor (a:Fin (n+1)) :
    forwardRoots (forwardCoord (Pi.single (.inl a) (1:R)))=
      Pi.single (.inl a) 1-Pi.single (.inl (0:Fin (n+1))) 1 := by
  induction a using Fin.induction with
  | zero =>
    have hz:forwardCoord (Pi.single (.inl (0:Fin (n+1))) (1:R))=0 := by
      ext g
      simp [forwardCoord_single,afterGap]
    rw [hz,map_zero,sub_self]
  | succ i ih =>
    simpa only [levelNode_last] using forwardRoots_coord_level i ih (Fin.last (i.val+2))

lemma forwardRoots_coord_vertex (a:Vertex n (Cell n)) :
    forwardRoots (forwardCoord (Pi.single a (1:R)))=Pi.single a 1-Pi.single (.inl (0:Fin (n+1))) 1 := by
  cases a with
  | inl a => exact forwardRoots_coord_anchor a
  | inr b =>
    let j:Fin (b.1.val+3):=⟨b.1.val+1-b.2.val,by have := b.2.isLt; omega⟩
    have hj:levelNode b.1 j=.inr b:=by
      have haq:=b.2.isLt
      simp only [levelNode,j]
      rw [dite_eq_right (by omega),dite_eq_right (by omega)]
      congr 1
      apply cell_ext
      · rfl
      change b.1.val+1-(b.1.val+1-b.2.val)=b.2.val
      omega
    simpa only [hj] using forwardRoots_coord_level b.1 (forwardRoots_coord_anchor b.1.castSucc) j

lemma vertexWeight_apply (m:Vertex n (Cell n) → R) : vertexWeight m=∑a,m a := by
  simp [vertexWeight,LinearMap.sum_apply]

lemma forwardRoots_coord (m:Vertex n (Cell n) → R) :
    forwardRoots (forwardCoord m)=m-vertexWeight m • Pi.single (.inl (0:Fin (n+1))) 1 := by
  have hm:m=∑a,m a • Pi.single a (1:R) := by
    ext a
    simp only [Finset.sum_apply,Pi.smul_apply,Pi.single_apply,smul_eq_mul]
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  calc
    _ = ∑a,m a • forwardRoots (forwardCoord (Pi.single a (1:R))) := by
      conv_lhs => rw [hm]
      simp only [map_sum,map_smul]
    _ = ∑a,m a • (Pi.single a (1:R)-Pi.single (.inl (0:Fin (n+1))) 1) := by
      simp_rw [forwardRoots_coord_vertex]
    _ = (∑a,m a • Pi.single a (1:R))-(∑a,m a • Pi.single (.inl (0:Fin (n+1))) 1) := by
      simp only [smul_sub,Finset.sum_sub_distrib]
    _ = _ := by rw [←hm,←Finset.sum_smul,vertexWeight_apply]

lemma forwardCoord_nonneg (m:Lattice n (Cell n)) (hm:∀a,0 ≤ m a) (g:GapIndex n) :
    0 ≤ forwardCoord m g := by
  rw [forwardCoord_apply]
  apply Finset.sum_nonneg
  intro a _
  split_ifs <;> first | exact hm a | omega

lemma triangularVertex_rootDegree (m:Lattice n (Cell n)) (hm:∀a,0 ≤ m a) :
    ∃k,HasRootDegree (forwardRoots (R:=ℤ) (n:=n)).toAddMonoidHom k (m-vertexWeight m • anchor 0) := by
  let c:GapIndex n → ℕ:=fun g=>(forwardCoord m g).toNat
  have hc:(fun g=>(c g:ℤ))=forwardCoord m := by
    ext g
    exact Int.toNat_of_nonneg (forwardCoord_nonneg m hm g)
  refine ⟨∑g,c g,c,rfl,?_⟩
  change forwardRoots (fun g=>(c g:ℤ))=m-vertexWeight m • anchor 0
  rw [hc,forwardRoots_coord]
  rfl
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularIncoming
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}

lemma initial_vertexDisplay (a:Vertex n (Cell n)) :
    vertexDisplay (includeVertices ∘ anchor) (includeVertices ∘ bridge) a=
      includeVertices (Pi.single a (1:ℤ)) := by cases a <;> rfl

lemma triangularSeed_nonneg {N:ℕ} (f:ElementaryExpr N)
    (m:Extended (Vertex n (Cell n))) (hm:m∈(triangularExpression f).support)
    (a:Vertex n (Cell n)) : 0 ≤ m.1 a := by
  let ell : Extended (Vertex n (Cell n)) →+ ℤ :=
    -((Pi.evalAddMonoidHom (fun _=>ℤ) a).comp (AddMonoidHom.fst _ _))
  have H:=f.cutSupported_scaled LaurentRay.vUnit (extendedOmega n) ell 0
    (vertexDisplay (includeVertices ∘ anchor) (includeVertices ∘ bridge)) (fun x=>by
      rw [initial_vertexDisplay]
      change -((Pi.single x (1:ℤ) : Lattice n (Cell n)) a) ≤ 0
      simp only [Pi.single_apply]
      split_ifs <;> omega) m hm
  change -(m.1 a) ≤ (N:ℤ)*0 at H
  omega

lemma triangularSeed_dual_zero {N:ℕ} (f:ElementaryExpr N)
    (m:Extended (Vertex n (Cell n))) (hm:m∈(triangularExpression f).support) : m.2=0 := by
  ext a
  let ell : Extended (Vertex n (Cell n)) →+ ℤ :=
    (Pi.evalAddMonoidHom (fun _=>ℤ) a).comp (AddMonoidHom.snd _ _)
  have H:=f.weight LaurentRay.vUnit (extendedOmega n) ell 0
    (vertexDisplay (includeVertices ∘ anchor) (includeVertices ∘ bridge)) (fun x=>by
      rw [initial_vertexDisplay]; rfl) m hm
  change m.2 a=(N:ℤ)*0 at H
  change m.2 a=0
  simpa only [mul_zero] using H

lemma triangularSeed_weight {N:ℕ} (f:ElementaryExpr N)
    (m:Extended (Vertex n (Cell n))) (hm:m∈(triangularExpression f).support) : vertexWeight m.1=(N:ℤ) := by
  let ell: Extended (Vertex n (Cell n)) →+ ℤ :=
    (vertexWeight (R:=ℤ)).toAddMonoidHom.comp (AddMonoidHom.fst _ _)
  have H:=f.weight LaurentRay.vUnit (extendedOmega n) ell 1
    (vertexDisplay (includeVertices ∘ anchor) (includeVertices ∘ bridge)) (fun x=>by
      rw [initial_vertexDisplay]
      change vertexWeight (Pi.single x (1:ℤ))=1
      simp [vertexWeight_apply,Pi.single_apply]) m hm
  change vertexWeight m.1=(N:ℤ)*1 at H
  simpa only [mul_one] using H

lemma triangularSeed_in_rootCone {N:ℕ} (f:ElementaryExpr N)
    (m:Extended (Vertex n (Cell n))) (hm:m∈(triangularExpression f).support) :
    ∃k,HasRootDegree (extendedRoots n) k (m-includeVertices ((N:ℤ) • anchor 0)) := by
  obtain ⟨k,c,hc,he⟩:=triangularVertex_rootDegree m.1 (triangularSeed_nonneg f m hm)
  refine ⟨k,c,hc,?_⟩
  change includeVertices (forwardRoots (fun i=>(c i:ℤ)))=m-includeVertices ((N:ℤ) • anchor 0)
  rw [triangularSeed_weight f m hm] at he
  change forwardRoots (fun i=>(c i:ℤ))=m.1-(N:ℤ) • anchor 0 at he
  rw [he,map_sub]
  congr 1
  exact Prod.ext rfl (triangularSeed_dual_zero f m hm).symm

lemma triangularIncoming_in_rootCone {N:ℕ} (f:ElementaryExpr N) (m:Lattice n (Cell n))
    (hm:triangularIncoming f m≠0) :
    ∃c:GapIndex n → ℕ, m=(N:ℤ) • anchor 0+forwardRoots (fun g=>(c g:ℤ)) := by
  obtain ⟨b,hb,d,hd⟩:=polynomialSection_support (extendedOmega n) extendedOmega_self
    (extendedRoots n) (extendedCoord n) (incomingCovector (extendedOmega n) (includeVertices m))
    (triangularExpression f) (includeVertices m) hm
  obtain ⟨k,hk⟩:=triangularSeed_in_rootCone f b hb
  have H:=rootDegree_add (extendedRoots n) hd hk
  rw [sub_add_sub_cancel] at H
  obtain ⟨c,_,he⟩:=H
  refine ⟨c,?_⟩
  have hh:forwardRoots (fun g=>(c g:ℤ))=m-(N:ℤ) • anchor 0 :=
    congrArg Prod.fst he
  rw [hh]
  abel
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularLinearIncoming
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}

lemma triangularLinear_locality_oai (m:Lattice n (Cell n)) (hm:triangularIncoming (.atom 1) m≠0) :
    triangularIncoming (.atom 1) m=triangularExpression (.atom 1) (includeVertices m) := by
  obtain ⟨c,hc⟩:=triangularIncoming_in_rootCone (.atom 1) m hm
  simp only [Nat.cast_one,one_smul] at hc
  obtain ⟨hK,hxi,_⟩:=triangularExpression_stationary (.atom 1) m hm
  exact actualPolynomialAdjoint_locality (extendedOmega n) extendedOmega_self
    (extendedRoots n) (extendedCoord n) extendedCoord_roots
    (rootSectionChart (extendedOmega n) (extendedRoots n) (incomingCovector (extendedOmega n) (includeVertices m)))
    (includeVertices (anchor 0)) (includeVertices m) c (by rw [hc,map_add]; rfl)
    (triangularExpression (.atom 1)) (by
      intro b hb
      simpa only [Nat.cast_one,one_smul] using triangularSeed_in_rootCone (.atom 1) b hb)
    (by intro g hg
        rw [extendedRoot_eq,extendedOmega_original]
        exact positive_gap_target_zero (fun i=>(c i:ℤ)) m (fun _=>Int.natCast_nonneg _) hc hK hxi g
          (by exact_mod_cast hg))

end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

theorem solution : type_of% @OAI.ElementaryPositivity.TriangularDynamics.triangularLinear_locality_oai := @OAI.ElementaryPositivity.TriangularDynamics.triangularLinear_locality_oai
