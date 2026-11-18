-- Prove2me | solution 1 for OAI.ElementaryPositivity.TriangularDynamics.triangularPower_incoming_retain
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T19:58:19.906199+00:00
-- url     : https://prove2.me/submissions/7f96dd1f-df47-4303-a8be-9a966bf73547

import Mathlib
import Definitions.Def_OAIQ368Chrom054
import Definitions.Def_OAIQ368Chrom058
import Theorems.Thm_OAI_ElementaryPositivity_TriangularDynamics_triangularPower_positive

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_TorusContinuity
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instAddCommGroup _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder _root_.OAI.ElementaryPositivity.RawShuffle.globalStringIndexLinearOrder _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
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

local instance instAddGroupTorusLaurentSeriesRat_r488a96_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_CompletedInverse
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne
attribute [-simp] _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.PowerSeriesAdjoint
open PowerSeries
noncomputable section
variable {A : Type*} [Ring A]
lemma inverse_mul (F G : PowerSeries A) (hF : constantCoeff F=1) (hG : constantCoeff G=1) :
    invOfUnit (F*G) 1=invOfUnit G 1*invOfUnit F 1 := by
  have hh : F*G*(invOfUnit G 1*invOfUnit F 1)=1:=by
    calc
      _=F*(G*invOfUnit G 1)*invOfUnit F 1:=by simp only [mul_assoc]
      _=1:=by rw [mul_invOfUnit G 1 hG,mul_one,mul_invOfUnit F 1 hF]
  calc
    _=invOfUnit (F*G) 1*(F*G*(invOfUnit G 1*invOfUnit F 1)):=by rw [hh,mul_one]
    _=(invOfUnit (F*G) 1*(F*G))*(invOfUnit G 1*invOfUnit F 1):=by simp only [mul_assoc]
    _=invOfUnit G 1*invOfUnit F 1:=by rw [invOfUnit_mul _ 1 (by simp [hF,hG]),one_mul]
lemma adjoint_mul (F G X : PowerSeries A) (hF : constantCoeff F=1) (hG : constantCoeff G=1) :
    adjoint (F*G) X=adjoint F (adjoint G X) := by
  simp only [adjoint,inverse_mul F G hF hG,mul_assoc]
end
end ElementaryPositivity.PowerSeriesAdjoint

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RootProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LaurentPositive
open LaurentPrecision
noncomputable section

lemma positive_zero : Positive 0 := fun _=>natCoeff_zero
lemma Positive.add {f g : LaurentSeries ℚ} (hf : Positive f) (hg : Positive g) : Positive (f+g) :=
  fun j=>(hf j).add (hg j)

lemma single (k : ℤ) (r : ℚ) (hr : NatCoeff r) : Positive (HahnSeries.single k r) := by
  intro j
  rw [HahnSeries.coeff_single]
  split <;> first | exact hr | exact natCoeff_zero

end
end ElementaryPositivity.LaurentPositive

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TorusPositive
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instAddCommGroup _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open LaurentPositive WallUnits PowerSeries
noncomputable section
variable {M : Type*} [AddCommGroup M]
variable (Ω : M →+ M →+ ℤ)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instAddCommMonoidTorusLaurentSeriesRatVUnit
local instance instAddGroupTorusLaurentSeriesRatVUnit_r488a96_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
lemma torusPositive_zero : TorusPositive Ω 0 := fun _=>positive_zero
lemma TorusPositive.add {f g : Torus LaurentRay.vUnit Ω}
    (hf : TorusPositive Ω f) (hg : TorusPositive Ω g) : TorusPositive Ω (f+g) :=
  fun m=>(hf m).add (hg m)
lemma TorusPositive.sum {A : Type*} (s : Finset A) (f : A → Torus LaurentRay.vUnit Ω)
    (h : ∀a∈s,TorusPositive Ω (f a)) : TorusPositive Ω (∑a∈s,f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact torusPositive_zero Ω
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add Ω (ih (fun b hb=>h b (Finset.mem_insert_of_mem hb)))
lemma torusPositive_monomial (m : M) (r : LaurentSeries ℚ) (hr : Positive r) :
    TorusPositive Ω (Torus.monomial LaurentRay.vUnit Ω m r) := by
  classical
  intro x
  change Positive ((Finsupp.single m r) x)
  by_cases h : m=x
  · subst x
    simpa only [Finsupp.single_eq_same] using hr
  · simpa only [Finsupp.single_eq_of_ne (Ne.symm h)] using positive_zero

lemma TorusPositive.mul {f g : Torus LaurentRay.vUnit Ω}
    (hf : TorusPositive Ω f) (hg : TorusPositive Ω g) : TorusPositive Ω (f*g) := by
  change TorusPositive Ω (Torus.multiply LaurentRay.vUnit Ω f g)
  unfold Torus.multiply Finsupp.sum
  apply TorusPositive.sum
  intro x hx
  apply TorusPositive.sum
  intro y hy
  apply torusPositive_monomial
  rw [LaurentRay.vUnit_zpow]
  exact ((hf x).mul (hg y)).mul (LaurentPositive.single _ _ natCoeff_one)

end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries LaurentPrecision
noncomputable section
variable {M I ι : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ)
variable (C : (I→ℤ) →+ M) (l : Filter ι)
attribute [local instance] Classical.propDecidable

local instance instAddGroupTorusLaurentSeriesRat_3_r488a96_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instSubTorusLaurentSeriesRat_3_r488a96_1 : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
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
local instance homogeneousElementaryExpressionsAddCommMonoid_r488a96_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
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

local instance elementaryExpressionBoundsRing_r488a96_1 : Ring (Torus v Ω) := Torus.instRing v Ω
local instance elementaryExpressionBoundsAddCommMonoid_r488a96_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance elementaryExpressionBoundsAddGroup_r488a96_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
local instance instAddCommMonoidTorus_1_r488a96_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_3_r488a96_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instNonUnitalSemiringTorus_r488a96_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_r488a96_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
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
local instance monomialConjugationAddCommMonoid_r488a96_1 : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance monomialConjugationAddGroup_r488a96_1 : AddGroup (Torus v Ω) :=
  (Torus.instRing v Ω).toAddGroup
lemma X_mul_X_neg (b:M) : Torus.X v Ω b*Torus.X v Ω (-b)=1 := by
  rw [Torus.X_mul_X_of_pairing_zero v Ω b (-b) (by simp only [map_neg,hΩ,neg_zero])]
  simp only [add_neg_cancel]
  rfl

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
local instance instAddCommMonoidTorus_2_r488a96_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_4_r488a96_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_MutationOrientedCompatibility
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M] (v : Rˣ) (Ω : M →+ M →+ ℤ)
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instRingTorus_3
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instAddCommMonoidTorus_4
local instance instAddGroupTorus_6_r488a96_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
lemma inverse_support_addSubmonoid (P : AddSubmonoid M) (f : PowerSeries (Torus v Ω))
    (hf : ∀n m,coeff n f m≠0 → m∈P) :
    ∀n m,coeff n (invOfUnit f 1) m≠0 → m∈P := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih=>
    intro m hm
    by_cases hn : n=0
    · subst n
      rw [coeff_invOfUnit,ite_eq_left rfl] at hm
      have hm0 : m=0:=by
        by_contra hh
        apply hm
        change Finsupp.single 0 (1:R) m=0
        exact Finsupp.single_eq_of_ne hh
      exact hm0 ▸ P.zero_mem
    · rw [coeff_invOfUnit,ite_eq_right hn] at hm
      simp only [inv_one,Units.val_one] at hm
      rw [torus_neg_one_mul] at hm
      change -(∑ab∈Finset.HasAntidiagonal.antidiagonal n,
        if ab.2<n then coeff ab.1 f*coeff ab.2 (invOfUnit f 1) else 0) m≠0 at hm
      have HH:=neg_ne_zero.mp hm
      rw [nonp_torus_eval_sum] at HH
      obtain ⟨ab,hab,hz⟩:=Finset.exists_ne_zero_of_sum_ne_zero HH
      have hb : ab.2<n:=by by_contra hh; simp [hh] at hz
      rw [ite_eq_left hb] at hz
      obtain ⟨a,b,ha,hb',he⟩:=torus_product_nonzero v Ω _ _ m hz
      exact he ▸ P.add_mem (hf ab.1 a ha) (ih ab.2 hb b hb')
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
local instance latticeHahnAddCommMonoid_r488a96_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance latticeHahnAddGroup_r488a96_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
local instance polynomialAdjointCoefficientsAddCommMonoid_r488a96_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance polynomialAdjointCoefficientsAddGroup_r488a96_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
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
local instance pureActualCoefficientsAddCommMonoid_r488a96_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance pureActualCoefficientsAddGroup_r488a96_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
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
local instance pureActualScalarCoefficientsAddCommMonoid_r488a96_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance pureActualScalarCoefficientsAddGroup_r488a96_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance pureActualScalarCoefficientsNonUnitalSemiring_r488a96_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
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
local instance halfspacePolynomialCoefficientsCoeffAddCommMonoid_r488a96_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance halfspacePolynomialCoefficientsCoeffAddGroup_r488a96_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance halfspacePolynomialCoefficientsCoeffNonUnitalSemiring_r488a96_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
local instance halfspacePolynomialCoefficientsCoeffNonUnitalNonAssocSemiring_r488a96_1 : NonUnitalNonAssocSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalNonAssocSemiring
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
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_PolynomialIncomingPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits PowerSeriesSplit
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ))

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRatVUnit_15
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_18_r488a96_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_18_r488a96_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
lemma rootSectionChart_action (h:M →+ ℝ) (X:PowerSeries (Torus LaurentRay.vUnit Ω)) :
    adjoint (rootSectionChart Ω C h).val X=
      sectionValue LaurentRay.vUnit Ω C (simpleTotalTransport Ω C) h
        (adjoint (invOfUnit (simpleTotalTransport Ω C).val 1) X) := by
  exact adjoint_mul _ _ _ (chartNegative LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C)).property.1 (by simp)

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_SectionIncoming
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
attribute [local instance] Classical.propDecidable
variable (F : CompletedPositive v Ω C) (b : M)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.sectionIncomingAddCommGroup
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.sectionIncomingAddGroup
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.sectionIncomingSub
lemma sectionIncoming_apply (n : ℕ) (X : PowerSeries (Torus v Ω)) (m : M) :
    sectionIncoming v Ω C F b n X m=if HasRootDegree C n (m-b) then
      (coeff n (sectionValue v Ω C F (incomingCovector Ω m) X)) m else 0 := rfl
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_HomogenizedPolynomialSection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries HahnSeries PowerSeriesAdjoint WallUnits
open Classical
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.homogenizedPolynomialSectionRing
local instance homogenizedPolynomialSectionAddCommMonoid_r488a96_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance homogenizedPolynomialSectionAddGroup_r488a96_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance homogenizedPolynomialSectionNonUnitalSemiring_r488a96_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.homogenizedPolynomialSectionNonUnitalNonAssocSemiring
lemma homogenize_hahn (τ:M →+ ℤ) (F:Torus LaurentRay.vUnit Ω)
    (hF:∀m,F m≠0 → 0 ≤ τ m) :
    HahnSeries.ofPowerSeries ℤ (Torus LaurentRay.vUnit Ω) (homogenize LaurentRay.vUnit Ω τ F)=
      latticeHahn LaurentRay.vUnit Ω τ F := by
  apply HahnSeries.ext
  funext j
  apply Finsupp.ext
  intro m
  rw [ofPowerSeries_coeff_int,latticeHahn_coeff]
  by_cases hf:F m=0
  · split_ifs <;> simp [homogenize_coeff,hf]
  · have hh:=hF m hf
    by_cases hj:0 ≤ j
    · rw [ite_eq_left hj,homogenize_coeff]
      have he:j.toNat=(τ m).toNat ↔ j=τ m:=by omega
      simp only [he]
    · rw [ite_eq_right hj]
      have he:j≠τ m:=by omega
      simp only [he,ite_false, if_false,Finsupp.zero_apply]

lemma ofPowerSeries_adjoint (f X:PowerSeries (Torus LaurentRay.vUnit Ω)) :
    HahnSeries.ofPowerSeries ℤ (Torus LaurentRay.vUnit Ω) (adjoint f X)=
      hahnAction f (HahnSeries.ofPowerSeries ℤ (Torus LaurentRay.vUnit Ω) X) := by
  simp only [adjoint,hahnAction,map_mul]

include hΩ in
lemma homogenize_adjoint_actual (τ:M →+ ℤ) (f:PowerSeries (Torus LaurentRay.vUnit Ω))
    (F:Torus LaurentRay.vUnit Ω) (hF:∀m,F m≠0 → 0 ≤ τ m) (m:M) (hm:0 ≤ τ m) :
    coeff (τ m).toNat (adjoint f (homogenize LaurentRay.vUnit Ω τ F)) m=
      actualPolynomialAdjointCoefficient Ω τ f F m := by
  rw [←hahnAction_actual_coeff Ω hΩ,←homogenize_hahn Ω τ F hF,←ofPowerSeries_adjoint,
    ofPowerSeries_coeff_int,ite_eq_left hm]

include hcoord in
omit [DecidableEq I] in
lemma conePolynomial_nonnegativeOrder (base:M) (hb:rootOrder coord base=0)
    (F:Torus LaurentRay.vUnit Ω) (hF:∀m,F m≠0 → ∃d,HasRootDegree C d (m-base)) :
    ∀m,F m≠0 → 0 ≤ rootOrder coord m := by
  intro m hm
  obtain ⟨d,hd⟩:=hF m hm
  have H:=rootOrder_eq C coord hcoord hd
  rw [map_sub,hb,sub_zero] at H
  rw [H]
  exact Int.natCast_nonneg _

include hΩ hcoord in
lemma polynomialInitial_incoming (base:M) (hb:rootOrder coord base=0)
    (F:Torus LaurentRay.vUnit Ω) (hF:∀m,F m≠0 → ∃d,HasRootDegree C d (m-base))
    (d:ℕ) (m:M) (hm:HasRootDegree C d (m-base)) :
    sectionIncoming LaurentRay.vUnit Ω C (simpleTotalTransport Ω C) base d (polynomialInitial Ω C coord F) m=
      polynomialSectionIncoming Ω C coord F m := by
  rw [sectionIncoming_apply,ite_eq_left hm]
  change coeff d (sectionValue LaurentRay.vUnit Ω C (simpleTotalTransport Ω C)
    (incomingCovector Ω m) (polynomialInitial Ω C coord F)) m=_
  unfold polynomialInitial
  rw [←rootSectionChart_action]
  have H:=rootOrder_eq C coord hcoord hm
  rw [map_sub,hb,sub_zero] at H
  have he:d=(rootOrder coord m).toNat:=by rw [H,Int.toNat_natCast]
  rw [he]
  exact homogenize_adjoint_actual Ω hΩ (rootOrder coord) _ F
    (conePolynomial_nonnegativeOrder Ω C coord hcoord base hb F hF) m (by rw [H]; omega)
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
open PowerSeries PowerSeriesAdjoint WallUnits
open Classical
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.rootSectionHalfspaceRing
local instance rootSectionHalfspaceAddCommMonoid_r488a96_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance rootSectionHalfspaceAddGroup_r488a96_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
lemma rootSectionChart_outer (h:M →+ ℝ) :
    (rootSectionChart Ω C h).val=invOfUnit
      ((chartPositive LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C)).val*
       (chartZero LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C)).val) 1 := by
  unfold rootSectionChart
  dsimp only
  conv_lhs => arg 2; arg 1; rw [←chart_three_factorization LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C)]
  rw [inverse_mul _ _ (by simp only [map_mul,
    (chartPositive LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C)).property.1,
    (chartZero LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C)).property.1,mul_one])
    (chartNegative LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C)).property.1,
    ←mul_assoc,mul_invOfUnit _ 1 (chartNegative LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C)).property.1,one_mul]

omit [DecidableEq I] in
lemma chartPositive_nonnegative [DecidableEq I] (h:M →+ ℝ) (F:CompletedPositive LaurentRay.vUnit Ω C)
    (k:ℕ) (m:M) (hm:coeff k (chartPositive LaurentRay.vUnit Ω C h F).val m≠0) : 0 ≤ h m := by
  cases k with
  | zero=>
    rw [coeff_zero_eq_constantCoeff,(chartPositive LaurentRay.vUnit Ω C h F).property.1] at hm
    have he:m=0:=by
      by_contra hn
      exact hm (Finsupp.single_eq_of_ne hn)
    rw [he,map_zero]
  | succ k=> exact (chart_three_support LaurentRay.vUnit Ω C h F).1 k m hm |>.le

omit [DecidableEq I] in
lemma chartZero_nonnegative [DecidableEq I] (h:M →+ ℝ) (F:CompletedPositive LaurentRay.vUnit Ω C)
    (k:ℕ) (m:M) (hm:coeff k (chartZero LaurentRay.vUnit Ω C h F).val m≠0) : 0 ≤ h m := by
  cases k with
  | zero=>
    rw [coeff_zero_eq_constantCoeff,(chartZero LaurentRay.vUnit Ω C h F).property.1] at hm
    have he:m=0:=by
      by_contra hn
      exact hm (Finsupp.single_eq_of_ne hn)
    rw [he,map_zero]
  | succ k=> rw [(chart_three_support LaurentRay.vUnit Ω C h F).2.1 k m hm]

lemma rootSectionChart_nonnegative (h:M →+ ℝ) (k:ℕ) (m:M)
    (hm:coeff k (rootSectionChart Ω C h).val m≠0) : 0 ≤ h m := by
  rw [rootSectionChart_outer] at hm
  let P:=nonpositiveCone (-h)
  have hs:∀d x,coeff d
      ((chartPositive LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C)).val*
       (chartZero LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C)).val) x≠0 → x∈P:=by
    intro d x hx
    obtain ⟨i,j,a,b,hij,ha,hb,he⟩:=series_product_nonzero LaurentRay.vUnit Ω _ _ d x hx
    change (-h) x ≤ 0
    rw [←he,map_add,AddMonoidHom.neg_apply,AddMonoidHom.neg_apply]
    linarith [chartPositive_nonnegative Ω C h (simpleTotalTransport Ω C) i a ha,
      chartZero_nonnegative Ω C h (simpleTotalTransport Ω C) j b hb]
  have H:=inverse_support_addSubmonoid LaurentRay.vUnit Ω P _ hs k m hm
  change -h m ≤ 0 at H
  linarith
end
end ElementaryPositivity.QuantumTorus

end
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
local instance targetCyclicAddGroup_r488a96_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_IndependentElement
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open scoped BigOperators
open Classical
noncomputable section
variable {K M V:Type*} [Field K] [AddCommGroup M] [Fintype V] [DecidableEq V]
variable (v:Kˣ) (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)

include hΩ in
omit [Fintype V] in
lemma independentTerm_singleton (w:V → M) (x:V) :
    independentTerm v Ω w 1 {x}=Torus.X v Ω (w x) := by
  have hi:IsIndependent Ω w {x}:=by
    intro a ha b hb
    simp only [Finset.mem_singleton] at ha hb
    subst a; subst b
    exact hΩ _
  simp only [independentTerm,hi,Finset.card_singleton,and_self,ite_true, if_true,setMonomial,Finset.sum_singleton]

include hΩ in
lemma independentElement_one (w:V → M) :
    independentElement v Ω w 1=∑x,Torus.X v Ω (w x) := by
  symm
  unfold independentElement
  apply Finset.sum_bij_ne_zero (fun x _ _=>({x}:Finset V))
  · intros; exact Finset.mem_univ _
  · intro x _ _ y _ _ h
    exact Finset.singleton_injective h
  · intro s _ hs
    unfold independentTerm at hs
    split_ifs at hs with H
    · obtain ⟨x,rfl⟩:=Finset.card_eq_one.mp H.2
      refine ⟨x,Finset.mem_univ _,?_,rfl⟩
      intro hh
      have Hx:=congrArg (fun F:Torus v Ω=>F (w x)) hh
      simp [Torus.X,Torus.monomial] at Hx
    · exact (hs rfl).elim
  · intro x _ _
    exact (independentTerm_singleton v Ω hΩ w x).symm
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FiniteLatticePairing
attribute [-instance] _root_.OAI.ElementaryPositivity.TriangularDynamics.instAntisymmCellPhaseLE _root_.OAI.ElementaryPositivity.TriangularDynamics.instDecidableRelCellPhaseLE _root_.OAI.ElementaryPositivity.TriangularDynamics.instIsTransCellPhaseLE _root_.OAI.ElementaryPositivity.TriangularDynamics.instTotalCellPhaseLE
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
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularScheduledRoots
attribute [-instance] _root_.OAI.ElementaryPositivity.TriangularDynamics.instAntisymmCellPhaseLE _root_.OAI.ElementaryPositivity.TriangularDynamics.instDecidableRelCellPhaseLE _root_.OAI.ElementaryPositivity.TriangularDynamics.instIsTransCellPhaseLE _root_.OAI.ElementaryPositivity.TriangularDynamics.instTotalCellPhaseLE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open scoped BigOperators

variable {n : ℕ}

lemma triangularOmega_skew (m m' : Lattice n (Cell n)) :
    triangularOmega n m m' = -triangularOmega n m' m :=
  matrixPairing_skew _ (chartMatrix_skew cellLevel triangularBB triangularBB_skew) _ _

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

end ElementaryPositivity.LatticeExtension

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_IncomingExtremalLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits
open Classical
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ))

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.incomingExtremalLocalityTorusRing
local instance incomingExtremalLocalityTorusAddCommMonoid_r488a96_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) :=
  (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance incomingExtremalLocalityTorusAddGroup_r488a96_1 : AddGroup (Torus LaurentRay.vUnit Ω) :=
  (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
lemma inverse_pairing_nonnegative (m:M) (f:PowerSeries (Torus LaurentRay.vUnit Ω))
    (hf:∀k r,coeff k f r≠0 → 0 ≤ Ω r m) :
    ∀k r,coeff k (invOfUnit f 1) r≠0 → 0 ≤ Ω r m := by
  intro k r hr
  let P:=nonpositiveCone (-(incomingCovector Ω m))
  have H:=inverse_support_addSubmonoid LaurentRay.vUnit Ω P f (by
    intro d x hx
    change -(Ω x m:ℝ) ≤ 0
    have hh:0 ≤ (Ω x m:ℝ):=by exact_mod_cast hf d x hx
    linarith) k r hr
  change -(Ω r m:ℝ) ≤ 0 at H
  have hh:0 ≤ (Ω r m:ℝ):=by linarith
  exact_mod_cast hh

include hΩ in
lemma adjoint_pairing_nonnegative (m b:M) (f:PowerSeries (Torus LaurentRay.vUnit Ω))
    (hf0:constantCoeff f=1) (hf:∀k r,coeff k f r≠0 → 0 ≤ Ω r m)
    (hb:0 ≤ Ω b m) (N:ℕ) :
    coeff N (adjoint f (PowerSeries.C (Torus.X LaurentRay.vUnit Ω b))) m=
      coeff N (PowerSeries.C (Torus.X LaurentRay.vUnit Ω b)) m := by
  apply adjoint_target_cyclic LaurentRay.vUnit Ω hΩ f b m N hf0
  intro i j hij r hr s hs he
  have h1:=hf i r (Finsupp.mem_support_iff.mp hr)
  have h2:=inverse_pairing_nonnegative Ω m f hf j s (Finsupp.mem_support_iff.mp hs)
  have H:Ω (r+(s+b)) m=0:=by rw [he,hΩ]
  simp only [map_add,AddMonoidHom.add_apply] at H
  omega

include hΩ in
lemma actualMonomialAdjoint_extremal (τ:M →+ ℤ) (m b:M)
    (f:PowerSeries (Torus LaurentRay.vUnit Ω))
    (hf0:constantCoeff f=1) (hf:∀k r,coeff k f r≠0 → 0 ≤ Ω r m)
    (hb:0 ≤ Ω b m) :
    actualMonomialAdjointCoefficient Ω τ f b m=actualMonomialAdjointCoefficient Ω τ 1 b m := by
  unfold actualMonomialAdjointCoefficient actualRootCoefficient
  split_ifs
  · have H1:=adjoint_monomial_coeff LaurentRay.vUnit Ω hΩ f b (m-b) ((τ (m-b)).toNat)
    have H2:=adjoint_monomial_coeff LaurentRay.vUnit Ω hΩ 1 b (m-b) ((τ (m-b)).toNat)
    rw [sub_add_cancel] at H1 H2
    rw [←H1,←H2,adjoint_pairing_nonnegative Ω hΩ m b f hf0 hf hb]
    have hi:invOfUnit (1:PowerSeries (Torus LaurentRay.vUnit Ω)) 1=1:=by
      simpa only [mul_one] using (invOfUnit_mul (1:PowerSeries (Torus LaurentRay.vUnit Ω)) 1 (by simp))
    simp only [adjoint,hi,one_mul,mul_one]
  · rfl

include hΩ in
lemma polynomialSectionIncoming_extremal (F:Torus LaurentRay.vUnit Ω) (m:M)
    (hF:∀b∈F.support,0 ≤ Ω b m) : polynomialSectionIncoming Ω C coord F m=F m := by
  rw [←actualPolynomialAdjointCoefficient_one Ω hΩ (rootOrder coord) F m]
  unfold polynomialSectionIncoming polynomialSectionCoefficient actualPolynomialAdjointCoefficient Finsupp.sum
  apply Finset.sum_congr rfl
  intro b hb
  apply congrArg (fun x=>F b*x)
  apply actualMonomialAdjoint_extremal Ω hΩ (rootOrder coord) m b _
    (rootSectionChart Ω C (incomingCovector Ω m)).property.1 _ (hF b hb)
  intro k r hr
  have H:=rootSectionChart_nonnegative Ω C (incomingCovector Ω m) k r hr
  change 0 ≤ (Ω r m:ℝ) at H
  exact_mod_cast H
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

variable (A : Matrix V V ℤ)

lemma realPairing_apply (x y : V → ℝ) :
    realPairing A x y=∑i,∑j,x i*(A i j:ℝ)*y j := Matrix.toBilin'_apply _ _ _

lemma realPairing_cast (x y : V → ℤ) :
    realPairing A (cast x) (cast y)=(matrixPairing A x y:ℝ) := by
  simp only [realPairing_apply,matrixPairing_apply,cast_apply,Int.cast_sum,Int.cast_mul]

lemma realDot_apply (x y : V → ℝ) : realDot x y=∑i,x i*y i := by
  simp [realDot,Matrix.toBilin'_apply,Matrix.one_apply]
lemma realDot_cast (x y : V → ℤ) :
    realDot (cast x) (cast y)=(LatticeExtension.dot x y:ℝ) := by
  simp only [realDot_apply,LatticeExtension.dot_apply,cast_apply,Int.cast_sum,Int.cast_mul]

omit [Fintype V] [DecidableEq V] in
lemma extendedCast_apply (x : LatticeExtension.Extended V) :
    extendedCast x=(cast x.1,cast x.2) := rfl

lemma extendedRealForm_apply (x y : (V → ℝ) × (V → ℝ)) :
    extendedRealForm A x y=realPairing A x.1 y.1+realDot x.2 y.1-realDot x.1 y.2 := rfl

lemma extendedRealForm_cast (x y : LatticeExtension.Extended V) :
    extendedRealForm A (extendedCast x) (extendedCast y)=
      (LatticeExtension.form (matrixPairing A) x y:ℝ) := by
  simp only [extendedRealForm_apply,extendedCast_apply,realPairing_cast,realDot_cast,
    LatticeExtension.form_apply,Int.cast_sub,Int.cast_add]

end ElementaryPositivity.LatticeRealization

end
section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus LatticeExtension LatticeRealization
open Classical
noncomputable section
variable {n:ℕ}

lemma extendedOmega_self : ∀m,extendedOmega n m m=0 := form_self _ triangularOmega_self
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

lemma triangularLinear_sum : triangularExpression (n:=n) (.atom 1)=
    ∑a:Vertex n (Cell n),Torus.X LaurentRay.vUnit (extendedOmega n)
      (includeVertices (Pi.single a (1:ℤ))) := by
  unfold triangularExpression ElementaryExpr.eval
  rw [independentElement_one _ _ extendedOmega_self]
  apply Finset.sum_congr rfl
  intro a _
  rw [initial_vertexDisplay]

end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularLinearSection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension PowerSeries PowerSeriesAdjoint
open Classical
noncomputable section
variable {n:ℕ}

lemma extendedCoord_anchor_zero : extendedCoord n (includeVertices (anchor 0))=0 := by
  ext g
  change forwardCoord (Pi.single (Sum.inl (0:Fin (n+1))) (1:ℤ)) g=0
  rw [forwardCoord_single]
  simp [afterGap]
lemma rootOrder_anchor_zero : rootOrder (extendedCoord n) (includeVertices (anchor 0))=0 := by
  change (∑g,extendedCoord n (includeVertices (anchor 0)) g)=0
  rw [extendedCoord_anchor_zero]
  simp
end
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}

lemma bridge_pair_pure (b:Cell n) (μ:Fin (n+1) → ℤ) :
    triangularOmega n (bridge b) (pureAnchor μ)=μ b.1.castSucc-μ b.1.succ := by
  have hroot:bridge b=eventRoot cellLevel 0 b+anchor b.1.castSucc:=by
    simp [eventRoot,cellLevel]
  rw [hroot,map_add,AddMonoidHom.add_apply,anchor_pair_pure,add_zero,pureAnchor,map_sum]
  simp only [map_zsmul,smul_eq_mul,eventRoot_anchor,mul_sub,Finset.sum_sub_distrib,mul_ite,mul_one,mul_zero]
  simp

lemma triangularSeed_dominant_nonnegative {N:ℕ} (f:ElementaryExpr N) (μ:Fin (n+1) → ℤ)
    (hμ:∀i:Fin n,μ i.succ ≤ μ i.castSucc) (m:Extended (Vertex n (Cell n)))
    (hm:m∈(triangularExpression f).support) : 0 ≤ extendedOmega n m (includeVertices (pureAnchor μ)) := by
  let ell:Extended (Vertex n (Cell n)) →+ ℤ:=
    -(AddMonoidHom.flip (extendedOmega n) (includeVertices (pureAnchor μ)))
  have H:=f.cutSupported_scaled LaurentRay.vUnit (extendedOmega n) ell 0
    (vertexDisplay (includeVertices ∘ anchor) (includeVertices ∘ bridge)) (by
      intro a
      rw [initial_vertexDisplay]
      change -(extendedOmega n (includeVertices (Pi.single a (1:ℤ))) (includeVertices (pureAnchor μ))) ≤ 0
      rw [extendedOmega_original]
      cases a with
      | inl a=> change -(triangularOmega n (anchor a) (pureAnchor μ)) ≤ 0; rw [anchor_pair_pure]; omega
      | inr b=> change -(triangularOmega n (bridge b) (pureAnchor μ)) ≤ 0; rw [bridge_pair_pure]; have := hμ b.1; omega) m hm
  change -(extendedOmega n m (includeVertices (pureAnchor μ))) ≤ (N:ℤ)*0 at H
  omega

lemma triangularPure_incoming {N:ℕ} (f:ElementaryExpr N) (μ:Fin (n+1) → ℤ)
    (hμ:∀i:Fin n,μ i.succ ≤ μ i.castSucc) :
    triangularIncoming f (pureAnchor μ)=triangularExpression f (includeVertices (pureAnchor μ)) := by
  apply polynomialSectionIncoming_extremal (extendedOmega n) extendedOmega_self (extendedRoots n) (extendedCoord n)
  intro m hm
  exact triangularSeed_dominant_nonnegative f μ hμ m hm
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularPositivePowers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension LatticeRealization PowerSeries PowerSeriesAdjoint LaurentPositive
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}

attribute [local instance] OAI.ElementaryPositivity.TriangularDynamics.triangularPositivePowersRing
local instance triangularPositivePowersAddCommMonoid_r488a96_1 : AddCommMonoid (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommMonoid
local instance triangularPositivePowersAddCommGroup_r488a96_1 : AddCommGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommGroup
local instance triangularPositivePowersAddGroup_r488a96_1 : AddGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddGroup
lemma linearPower_eval (N:ℕ) :
    triangularExpression (n:=n) (linearPower N)=(triangularExpression (.atom 1))^N := by
  induction N with
  | zero=>rfl
  | succ N ih=>change triangularExpression (linearPower N)*triangularExpression (.atom 1)=_; rw [ih,pow_succ]

lemma triangularPower_incoming_positive (N k:ℕ) :
    TorusPositive (extendedOmega n)
      (sectionIncoming LaurentRay.vUnit (extendedOmega n) (extendedRoots n)
        (simpleTotalTransport (extendedOmega n) (extendedRoots n))
        (includeVertices ((N:ℤ) • anchor 0)) k
        (polynomialInitial (extendedOmega n) (extendedRoots n) (extendedCoord n)
          (triangularExpression (linearPower N)))) := by
  intro m
  rw [sectionIncoming_apply]
  split_ifs
  · have hcov:(((triangularRealForm n).flip (extendedCast m)).toAddMonoidHom.comp extendedCast) = incomingCovector (extendedOmega n) m := by
      ext a
      exact triangularRealForm_compatible a m
    have H:=triangularPower_positive (n:=n) N ((triangularRealForm n).flip (extendedCast m)) k m
    rw [hcov,rootSectionChart_action] at H
    exact H
  · exact positive_zero
end
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension PowerSeries PowerSeriesAdjoint LaurentPositive
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}

attribute [local instance] OAI.ElementaryPositivity.TriangularDynamics.triangularOrdinaryPowersRing
attribute [local instance] OAI.ElementaryPositivity.TriangularDynamics.triangularOrdinaryPowersAddCommMonoid
attribute [local instance] OAI.ElementaryPositivity.TriangularDynamics.triangularOrdinaryPowersAddCommGroup
attribute [local instance] OAI.ElementaryPositivity.TriangularDynamics.triangularOrdinaryPowersAddGroup
attribute [local instance] OAI.ElementaryPositivity.TriangularDynamics.triangularOrdinaryPowersSub
lemma triangularLinear_ordinary_positive : TorusPositive (extendedOmega n) (triangularExpression (.atom 1)) := by
  rw [triangularLinear_sum]
  exact TorusPositive.sum _ _ _ (fun a _=>torusPositive_monomial _ _ _ positive_one)

lemma triangularLinear_retain (a:Fin (n+1)) :
    TorusPositive (extendedOmega n)
      (triangularExpression (.atom 1)-Torus.X LaurentRay.vUnit (extendedOmega n) (includeVertices (anchor a))) := by
  have H:(∑b∈(Finset.univ:Finset (Vertex n (Cell n))).erase (.inl a),
      Torus.X LaurentRay.vUnit (extendedOmega n) (includeVertices (Pi.single b (1:ℤ))))=
      triangularExpression (.atom 1)-Torus.X LaurentRay.vUnit (extendedOmega n) (includeVertices (anchor a)) := by
    apply Finsupp.ext
    intro m
    rw [torus_sub_apply,triangularLinear_sum]
    simp only [Finsupp.finsetSum_apply]
    have H:=Finset.sum_erase_add
      (s:=(Finset.univ:Finset (Vertex n (Cell n))))
      (fun b=>(Torus.X LaurentRay.vUnit (extendedOmega n) (includeVertices (Pi.single b (1:ℤ)))) m)
      (Finset.mem_univ (.inl a))
    change _ = _ - (Torus.X LaurentRay.vUnit (extendedOmega n) (includeVertices (Pi.single (.inl a) (1:ℤ)))) m
    rw [←H,add_sub_cancel_right]
    let ev:Torus LaurentRay.vUnit (extendedOmega n) →+ LaurentSeries ℚ :=
      {toFun:=fun f=>f m,map_zero':=rfl,map_add':=fun _ _=>rfl}
    exact map_sum ev _ _
  rw [←H]
  exact TorusPositive.sum _ _ _ (fun b _=>torusPositive_monomial _ _ _ positive_one)

lemma natAnchor_zero : natAnchor (n:=n) 0=0 := by
  ext a
  cases a <;> simp [natAnchor,pureAnchor_apply_anchor,pureAnchor_apply_bridge]

lemma natAnchor_step (μ:Fin (n+1) → ℕ) (a:Fin (n+1)) (ha:0<μ a) :
    natAnchor μ=natAnchor (Function.update μ a (μ a-1))+anchor a := by
  ext b
  cases b with
  | inl b=>
    simp only [natAnchor,pureAnchor_apply_anchor,Pi.add_apply,anchor,Pi.single_apply,Sum.inl.injEq]
    by_cases hb:b=a
    · subst b; simp only [Function.update_self,ite_true, if_true]; omega
    · rw [Function.update_of_ne hb,ite_eq_right hb]
      simp
  | inr b=>simp [natAnchor,pureAnchor_apply_bridge,anchor]

lemma natural_sum_step (μ:Fin (n+1) → ℕ) (a:Fin (n+1)) (ha:0<μ a) :
    (∑b,Function.update μ a (μ a-1) b)+1=∑b,μ b := by
  symm
  calc
    _ = ∑b,(Function.update μ a (μ a-1) b+(if b=a then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb:b=a
      · subst b; simp only [Function.update_self,ite_true, if_true]; omega
      · rw [Function.update_of_ne hb,ite_eq_right hb]; omega
    _ = _ := by rw [Finset.sum_add_distrib]; simp

lemma triangularPower_ordinary_retain (N:ℕ) (μ:Fin (n+1) → ℕ) (hμ:∑a,μ a=N) :
    TorusPositive (extendedOmega n)
      (triangularExpression (linearPower N)-Torus.X LaurentRay.vUnit (extendedOmega n) (includeVertices (natAnchor μ))) := by
  induction N generalizing μ with
  | zero=>
    have hz:μ=0:=by
      ext a
      have H:μ a ≤ ∑b,μ b:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ a)
      have H':μ a=0:=by omega
      exact H'
    subst μ
    rw [natAnchor_zero,map_zero,Torus.X_zero,linearPower_eval,pow_zero,sub_self]
    exact torusPositive_zero _
  | succ N ih=>
    obtain ⟨a,_,ha⟩:=Finset.exists_ne_zero_of_sum_ne_zero (show (∑a,μ a)≠0 by omega)
    have ha':0<μ a:=Nat.pos_of_ne_zero ha
    let ν:=Function.update μ a (μ a-1)
    have hν:∑b,ν b=N:=by
      change (∑b,Function.update μ a (μ a-1) b)=N
      have :=natural_sum_step μ a ha'
      omega
    have hp:(triangularExpression (linearPower N)-Torus.X LaurentRay.vUnit (extendedOmega n) (includeVertices (natAnchor ν)))*
        triangularExpression (.atom 1)+Torus.X LaurentRay.vUnit (extendedOmega n) (includeVertices (natAnchor ν))*
        (triangularExpression (.atom 1)-Torus.X LaurentRay.vUnit (extendedOmega n) (includeVertices (anchor a)))=
        triangularExpression (linearPower (N+1))-Torus.X LaurentRay.vUnit (extendedOmega n) (includeVertices (natAnchor μ)):=by
      have hpair:extendedOmega n (includeVertices (natAnchor ν)) (includeVertices (anchor a))=0:=by
        rw [extendedOmega_original,triangularOmega_skew,natAnchor,anchor_pair_pure,neg_zero]
      have hm:Torus.X LaurentRay.vUnit (extendedOmega n) (includeVertices (natAnchor ν))*
          Torus.X LaurentRay.vUnit (extendedOmega n) (includeVertices (anchor a))=
          Torus.X LaurentRay.vUnit (extendedOmega n) (includeVertices (natAnchor μ)):=by
        rw [Torus.X_mul_X_of_pairing_zero _ _ _ _ hpair,←map_add,←natAnchor_step μ a ha']
      change (_-_)*_+_*(_-_)=triangularExpression (linearPower N)*triangularExpression (.atom 1)-_
      calc
        _ = triangularExpression (linearPower N)*triangularExpression (.atom 1)-
            Torus.X LaurentRay.vUnit (extendedOmega n) (includeVertices (natAnchor ν))*
            Torus.X LaurentRay.vUnit (extendedOmega n) (includeVertices (anchor a)) := by noncomm_ring
        _ = _ := by rw [hm]
    rw [←hp]
    exact ((ih ν hν).mul _ triangularLinear_ordinary_positive).add _
      ((torusPositive_monomial _ _ _ positive_one).mul _ (triangularLinear_retain a))
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_LaurentPositiveDomination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension LatticeRealization PowerSeries PowerSeriesAdjoint LaurentPositive
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}
attribute [local instance] OAI.ElementaryPositivity.TriangularDynamics.instRingTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega
attribute [local instance] OAI.ElementaryPositivity.TriangularDynamics.instAddCommMonoidTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega
attribute [local instance] OAI.ElementaryPositivity.TriangularDynamics.instAddCommGroupTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega
attribute [local instance] OAI.ElementaryPositivity.TriangularDynamics.instAddGroupTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega
attribute [local instance] OAI.ElementaryPositivity.TriangularDynamics.instSubTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega
lemma triangularBase_order (N:ℕ) : rootOrder (extendedCoord n) (triangularBase N)=0 := by
  rw [triangularBase,map_zsmul,map_zsmul,rootOrder_anchor_zero,zsmul_zero]
lemma triangularPower_incoming_retain_oai (N:ℕ) (μ:Fin (n+1) → ℕ) (hμ:∑a,μ a=N)
    (hdom:∀i:Fin n,μ i.succ ≤ μ i.castSucc) (d:ℕ)
    (hm:HasRootDegree (extendedRoots n) d (includeVertices (natAnchor μ)-triangularBase N)) (k:ℕ) :
    TorusPositive (extendedOmega n)
      (sectionIncoming LaurentRay.vUnit (extendedOmega n) (extendedRoots n)
        (simpleTotalTransport (extendedOmega n) (extendedRoots n)) (triangularBase N) k
        (polynomialInitial (extendedOmega n) (extendedRoots n) (extendedCoord n) (triangularExpression (linearPower N)))-
        coneDelta (extendedOmega n) d (includeVertices (natAnchor μ)) k) := by
  by_cases hk:k=d
  · subst k
    rw [coneDelta,ite_eq_left rfl]
    intro m
    rw [torus_sub_apply]
    by_cases he:m=includeVertices (natAnchor μ)
    · subst m
      rw [polynomialInitial_incoming (extendedOmega n) extendedOmega_self (extendedRoots n)
        (extendedCoord n) extendedCoord_roots (triangularBase N) (triangularBase_order N)
        (triangularExpression (linearPower N)) (by intro m hm; exact triangularSeed_in_rootCone _ m (Finsupp.mem_support_iff.mpr hm)) d _ hm]
      have H:=triangularPure_incoming (linearPower N) (fun a=>(μ a:ℤ)) (fun i=>Int.ofNat_le.mpr (hdom i))
      change polynomialSectionIncoming _ _ _ _ (includeVertices (natAnchor μ))=_ at H
      rw [H]
      simpa only [torus_sub_apply,natAnchor] using triangularPower_ordinary_retain N μ hμ (includeVertices (natAnchor μ))
    · have HX:Torus.X LaurentRay.vUnit (extendedOmega n) (includeVertices (natAnchor μ)) m=0:=by
        exact Finsupp.single_eq_of_ne he
      rw [HX,sub_zero]
      exact triangularPower_incoming_positive N d m
  · rw [coneDelta,ite_eq_right hk,sub_zero]
    exact triangularPower_incoming_positive N k

end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

theorem solution : type_of% @OAI.ElementaryPositivity.TriangularDynamics.triangularPower_incoming_retain_oai := @OAI.ElementaryPositivity.TriangularDynamics.triangularPower_incoming_retain_oai
