-- Prove2me | solution 1 for OAI.ElementaryPositivity.TriangularDynamics.triangularIncoming_anchorCoeff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:58:45.375783+00:00
-- url     : https://prove2.me/submissions/60a1bc3e-4896-4dd9-be04-d27c89e294ff

import Mathlib
import Definitions.Def_OAIQ368Chrom058

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

local instance instAddGroupTorusLaurentSeriesRat_r029fe4_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
end
end ElementaryPositivity.PowerSeriesAdjoint

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

local instance instAddGroupTorusLaurentSeriesRat_3_r029fe4_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instSubTorusLaurentSeriesRat_3_r029fe4_1 : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
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
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_IndependentSetElements
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
attribute [-simp] _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
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
variable {K M V W : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ)

lemma sum_labels_disjSum (u : V → M) (w : W → M) (s : Finset V) (t : Finset W) :
    (∑ x ∈ s.disjSum t,Sum.elim u w x)=(∑x∈s,u x)+(∑y∈t,w y) := by
  simp

lemma independent_sum_decomposition [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (u : V → M) (w : W → M) (k : ℕ) :
    independentElement v Ω (Sum.elim u w) k =
      ∑ t : Finset W,∑ s : Finset V, independentTerm v Ω (Sum.elim u w) k (s.disjSum t) := by
  unfold independentElement
  rw [←Equiv.sum_comp (Finset.sumEquiv : Finset (V⊕W) ≃o Finset V×Finset W).symm.toEquiv]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  rfl

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
local instance homogeneousElementaryExpressionsAddCommMonoid_r029fe4_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
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

local instance elementaryExpressionBoundsRing_r029fe4_1 : Ring (Torus v Ω) := Torus.instRing v Ω
local instance elementaryExpressionBoundsAddCommMonoid_r029fe4_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance elementaryExpressionBoundsAddGroup_r029fe4_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
local instance instAddCommMonoidTorus_1_r029fe4_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_3_r029fe4_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instNonUnitalSemiringTorus_r029fe4_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_r029fe4_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
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
local instance monomialConjugationAddCommMonoid_r029fe4_1 : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance monomialConjugationAddGroup_r029fe4_1 : AddGroup (Torus v Ω) :=
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
local instance instAddCommMonoidTorus_2_r029fe4_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_4_r029fe4_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
local instance instAddGroupTorus_6_r029fe4_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
local instance latticeHahnAddCommMonoid_r029fe4_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance latticeHahnAddGroup_r029fe4_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
local instance polynomialAdjointCoefficientsAddCommMonoid_r029fe4_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance polynomialAdjointCoefficientsAddGroup_r029fe4_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
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
local instance pureActualCoefficientsAddCommMonoid_r029fe4_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance pureActualCoefficientsAddGroup_r029fe4_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
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
local instance pureActualScalarCoefficientsAddCommMonoid_r029fe4_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance pureActualScalarCoefficientsAddGroup_r029fe4_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance pureActualScalarCoefficientsNonUnitalSemiring_r029fe4_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
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
local instance halfspacePolynomialCoefficientsCoeffAddCommMonoid_r029fe4_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance halfspacePolynomialCoefficientsCoeffAddGroup_r029fe4_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance halfspacePolynomialCoefficientsCoeffNonUnitalSemiring_r029fe4_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
local instance halfspacePolynomialCoefficientsCoeffNonUnitalNonAssocSemiring_r029fe4_1 : NonUnitalNonAssocSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalNonAssocSemiring
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
open PowerSeries PowerSeriesAdjoint WallUnits
open Classical
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.rootSectionHalfspaceRing
local instance rootSectionHalfspaceAddCommMonoid_r029fe4_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance rootSectionHalfspaceAddGroup_r029fe4_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
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
local instance targetCyclicAddGroup_r029fe4_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
local instance incomingExtremalLocalityTorusAddCommMonoid_r029fe4_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) :=
  (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance incomingExtremalLocalityTorusAddGroup_r029fe4_1 : AddGroup (Torus LaurentRay.vUnit Ω) :=
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
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RealLatticeRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus LatticeExtension LatticeRealization
open Classical
noncomputable section
variable {n:ℕ}

lemma extendedOmega_self : ∀m,extendedOmega n m m=0 := form_self _ triangularOmega_self
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
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularMonomialCriterion
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
attribute [local instance] OAI.ElementaryPositivity.TriangularDynamics.instRingTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega_2
local instance instAddCommMonoidTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega_2_r029fe4_1 : AddCommMonoid (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommMonoid
local instance instAddCommGroupTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega_2_r029fe4_1 : AddCommGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommGroup
local instance instAddGroupTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega_2_r029fe4_1 : AddGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddGroup
local instance instSubTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega_2_r029fe4_1 : Sub (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toSub
lemma anchorExponent_injective : Function.Injective (anchorExponent (n:=n)) := by
  intro d e he
  ext a
  have H:=congrArg (fun m:Extended (Vertex n (Cell n))=>m.1 (.inl a)) he
  change pureAnchor (fun a=>(d a:ℤ)) (.inl a)=pureAnchor (fun a=>(e a:ℤ)) (.inl a) at H
  rw [pureAnchor_apply_anchor,pureAnchor_apply_anchor] at H
  exact Int.ofNat_inj.mp H
lemma anchorPolynomial_coeff (p:MvPolynomial (Fin (n+1)) (LaurentSeries ℚ)) (d:Fin (n+1) →₀ ℕ) :
    anchorPolynomialAdd p (anchorExponent d)=p.coeff d :=
  Finsupp.mapDomain_apply anchorExponent_injective (AddMonoidAlgebra.coeff p) d
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularAnchorProjection
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

attribute [local instance] OAI.ElementaryPositivity.TriangularDynamics.triangularAnchorProjectionRing
attribute [local instance] OAI.ElementaryPositivity.TriangularDynamics.triangularAnchorProjectionAddCommMonoid
attribute [local instance] OAI.ElementaryPositivity.TriangularDynamics.triangularAnchorProjectionAddCommGroup
attribute [local instance] OAI.ElementaryPositivity.TriangularDynamics.triangularAnchorProjectionAddGroup
local instance triangularAnchorProjectionSub_r029fe4_1 : Sub (Torus LaurentRay.vUnit (extendedOmega n)) :=
  (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toSub
lemma bridgeCut_anchor (a:Fin (n+1)) : bridgeCut (includeVertices (anchor a))=0 := by
  simp [bridgeCut,anchor]
lemma bridgeCut_bridge (b:Cell n) : bridgeCut (includeVertices (bridge b))= -1 := by
  simp [bridgeCut,bridge,Pi.single_apply]
lemma bridgeCut_pure (μ:Fin (n+1) → ℤ) : bridgeCut (includeVertices (pureAnchor μ))=0 := by
  simp only [pureAnchor,map_sum,map_zsmul,bridgeCut_anchor,zsmul_zero,Finset.sum_const_zero]

lemma triangularSeed_bridgeCut {N:ℕ} (f:ElementaryExpr N) :
    triangularExpression f∈supportedSubring LaurentRay.vUnit (extendedOmega n) (nonpositiveCone bridgeCut) := by
  intro m hm
  by_contra hn
  apply hm
  change -(∑b:Cell n,(m.1 (.inr b):ℝ)) ≤ 0
  apply neg_nonpos.mpr
  apply Finset.sum_nonneg
  intro b _
  exact_mod_cast triangularSeed_nonneg f m (Finsupp.mem_support_iff.mpr hn) (.inr b)

lemma anchorExponent_single (a:Fin (n+1)) :
    anchorExponent (Finsupp.single a 1)=includeVertices (anchor a) := by
  apply Prod.ext
  · ext b
    cases b with
    | inl b=>simp [anchorExponent,pureAnchor_apply_anchor,anchor,Pi.single_apply,Finsupp.single_apply,eq_comm]
    | inr b=>simp [anchorExponent,pureAnchor_apply_bridge,anchor]
  · rfl

lemma anchorPolynomial_esymm (k:ℕ) :
    anchorPolynomial (MvPolynomial.esymm (Fin (n+1)) (LaurentSeries ℚ) k)=
      ∑s:Finset (Fin (n+1)),if s.card=k then
        Torus.X LaurentRay.vUnit (extendedOmega n) (∑a∈s,includeVertices (anchor a)) else 0 := by
  rw [MvPolynomial.esymm_eq_sum_monomial,map_sum]
  have he:Finset.powersetCard k (Finset.univ:Finset (Fin (n+1)))=
      (Finset.univ:Finset (Finset (Fin (n+1)))).filter (fun s=>s.card=k):=by ext s; simp
  rw [he,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s _
  split_ifs
  · change anchorPolynomialAdd (MvPolynomial.monomial _ 1)=_
    rw [anchorPolynomial_monomial,map_sum]
    simp only [anchorExponent_single,Torus.X]
  · rfl

lemma independent_projection_pair (k:ℕ) (s:Finset (Fin (n+1))) (t:Finset (Cell n)) :
    zeroProject LaurentRay.vUnit (extendedOmega n) bridgeCut
      (independentTerm LaurentRay.vUnit (extendedOmega n)
        (vertexDisplay (includeVertices ∘ anchor) (includeVertices ∘ bridge)) k (s.disjSum t))=
      if t=∅ then (if s.card=k then
        Torus.X LaurentRay.vUnit (extendedOmega n) (∑a∈s,includeVertices (anchor a)) else 0) else 0 := by
  have hsum:(∑x∈s.disjSum t,vertexDisplay (includeVertices ∘ anchor) (includeVertices ∘ bridge) x)=
      (∑a∈s,includeVertices (anchor a))+(∑b∈t,includeVertices (bridge b)):=by
    exact sum_labels_disjSum _ _ s t
  have hcut:bridgeCut (∑x∈s.disjSum t,vertexDisplay (includeVertices ∘ anchor) (includeVertices ∘ bridge) x)= -(t.card:ℝ):=by
    rw [hsum,map_add,map_sum,map_sum]
    simp only [bridgeCut_anchor,bridgeCut_bridge,Finset.sum_const_zero,zero_add,Finset.sum_const,nsmul_eq_mul,mul_neg,mul_one]
  by_cases ht:t=∅
  · subst t
    have hind:IsIndependent (extendedOmega n)
        (vertexDisplay (includeVertices ∘ anchor) (includeVertices ∘ bridge)) (s.disjSum ∅):=by
      intro x hx y hy
      obtain ⟨a,ha,rfl⟩:=Finset.mem_disjSum.mp hx |>.resolve_right (by simp)
      obtain ⟨b,hb,rfl⟩:=Finset.mem_disjSum.mp hy |>.resolve_right (by simp)
      change extendedOmega n (includeVertices (anchor a)) (includeVertices (anchor b))=0
      rw [extendedOmega_original]
      exact omega_anchors a b
    simp only [independentTerm,hind,true_and,Finset.card_disjSum,Finset.card_empty,add_zero,ite_true, if_true]
    split_ifs with hc
    · rw [setMonomial,Torus.X,zeroProject_monomial,show bridgeCut (∑x∈s.disjSum ∅,vertexDisplay (includeVertices ∘ anchor) (includeVertices ∘ bridge) x)=0 by simpa using hcut,ite_eq_left rfl,hsum]
      simp only [Finset.sum_empty,add_zero,Torus.X]
    · exact map_zero _
  · rw [ite_eq_right ht,independentTerm]
    split_ifs
    · rw [setMonomial,Torus.X,zeroProject_monomial,ite_eq_right]
      rw [hcut]
      simpa only [neg_eq_zero,Nat.cast_eq_zero,Finset.card_eq_zero] using ht
    · exact map_zero _

lemma triangularAtom_projection (k:ℕ) :
    zeroProject LaurentRay.vUnit (extendedOmega n) bridgeCut (triangularExpression (.atom k))=
      anchorPolynomial (MvPolynomial.esymm (Fin (n+1)) (LaurentSeries ℚ) k) := by
  change zeroProject _ _ _ (independentElement _ _ (Sum.elim _ _) k)=_
  rw [independent_sum_decomposition]
  change zeroProject _ _ _ (∑t:Finset (Cell n),∑s:Finset (Fin (n+1)),
    independentTerm LaurentRay.vUnit (extendedOmega n)
      (vertexDisplay (includeVertices ∘ anchor) (includeVertices ∘ bridge)) k (s.disjSum t))=_
  rw [map_sum,anchorPolynomial_esymm]
  simp only [map_sum,independent_projection_pair]
  rw [Finset.sum_eq_single (∅:Finset (Cell n))]
  · simp only [ite_true, if_true]
  · intro t _ ht
    simp only [ite_eq_right ht,Finset.sum_const_zero]
  · simp

lemma triangularExpression_projection {N:ℕ} (f:ElementaryExpr N) :
    zeroProject LaurentRay.vUnit (extendedOmega n) bridgeCut (triangularExpression f)=
      anchorPolynomial (f.ordinary (σ:=Fin (n+1)) (R:=LaurentSeries ℚ)) := by
  induction f with
  | zero k=>exact (map_zero _).trans (map_zero _).symm
  | one=>exact (zeroProject_one _ _ _).trans (map_one _).symm
  | atom k=>exact triangularAtom_projection k
  | add f g hf hg=>simpa only [triangularExpression,ElementaryExpr.eval,ElementaryExpr.ordinary,map_add] using congrArg₂ (fun a b=>a+b) hf hg
  | neg f hf=>simpa only [triangularExpression,ElementaryExpr.eval,ElementaryExpr.ordinary,map_neg] using congrArg Neg.neg hf
  | mul f g hf hg=>
    change zeroProject _ _ _ (triangularExpression f*triangularExpression g)=anchorPolynomial (f.ordinary*g.ordinary)
    rw [zeroProject_mul_nonpositive _ _ _ _ _ (triangularSeed_bridgeCut f) (triangularSeed_bridgeCut g),hf,hg,map_mul]

lemma triangularExpression_anchorCoeff {N:ℕ} (f:ElementaryExpr N) (d:Fin (n+1) →₀ ℕ) :
    triangularExpression f (anchorExponent d)=(f.ordinary (σ:=Fin (n+1)) (R:=LaurentSeries ℚ)).coeff d := by
  have H:=congrArg (fun t:Torus LaurentRay.vUnit (extendedOmega n)=>t (anchorExponent d)) (triangularExpression_projection (n:=n) f)
  rw [show (anchorPolynomial (f.ordinary (σ:=Fin (n+1)) (R:=LaurentSeries ℚ))) (anchorExponent d)=
    (f.ordinary (σ:=Fin (n+1)) (R:=LaurentSeries ℚ)).coeff d from anchorPolynomial_coeff _ d] at H
  change ((triangularExpression f).filter (fun m=>bridgeCut m=0)) (anchorExponent d)=_ at H
  simpa only [Finsupp.filter_apply,show bridgeCut (anchorExponent d)=0 from bridgeCut_pure _,ite_true, if_true] using H
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Histories_TriangularCommonHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension LatticeRealization PowerSeries PowerSeriesAdjoint
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}

lemma triangularIncoming_anchorCoeff_oai {N:ℕ} (f:ElementaryExpr N) (μ:Fin (n+1) →₀ ℕ)
    (hμ:∀i:Fin n,μ i.succ≤μ i.castSucc) :
    polynomialSectionIncoming (extendedOmega n) (extendedRoots n) (extendedCoord n)
      (triangularExpression f) (anchorExponent μ)=
      (f.ordinary (σ:=Fin (n+1)) (R:=LaurentSeries ℚ)).coeff μ := by
  rw [←triangularExpression_anchorCoeff f μ]
  exact triangularPure_incoming f (fun a=>(μ a:ℤ)) (fun i=>Int.ofNat_le.mpr (hμ i))

end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

theorem solution : type_of% @OAI.ElementaryPositivity.TriangularDynamics.triangularIncoming_anchorCoeff_oai := @OAI.ElementaryPositivity.TriangularDynamics.triangularIncoming_anchorCoeff_oai
