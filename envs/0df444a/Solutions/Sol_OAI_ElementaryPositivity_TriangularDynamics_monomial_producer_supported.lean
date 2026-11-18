-- Prove2me | solution 1 for OAI.ElementaryPositivity.TriangularDynamics.monomial_producer_supported
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:58:01.47754+00:00
-- url     : https://prove2.me/submissions/5140b74a-4e8a-4021-961a-f6c09b4a815b

import Mathlib
import Definitions.Def_OAIQ368Chrom058
import Theorems.Thm_OAI_ElementaryPositivity_TriangularDynamics_triangularMonomial_initial

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

local instance instAddGroupTorusLaurentSeriesRat_rba43ae_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instAddCommGroup _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne
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
lemma coeff_mul_vanish_right (F U : PowerSeries A) (n : ℕ) (hU : ∀j<n,coeff j U=0) :
    coeff n (F*U)=constantCoeff F*coeff n U := by
  classical
  rw [coeff_mul,Finset.sum_eq_single (0,n)]
  · simp only [coeff_zero_eq_constantCoeff]
  · intro p hp hpn
    have H:=Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hx : p.2<n:=by
      by_contra hh
      have hp0 : p.1=0:=by omega
      have hp2 : p.2=n:=by omega
      exact hpn (Prod.ext hp0 hp2)
    rw [hU p.2 hx,mul_zero]
  · intro hn
    exact (hn (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by simp))).elim
lemma coeff_mul_vanish_left (U F : PowerSeries A) (n : ℕ) (hU : ∀j<n,coeff j U=0) :
    coeff n (U*F)=coeff n U*constantCoeff F := by
  classical
  rw [coeff_mul,Finset.sum_eq_single (n,0)]
  · simp only [coeff_zero_eq_constantCoeff]
  · intro p hp hpn
    have H:=Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hx : p.1<n:=by
      by_contra hh
      have hp0 : p.2=0:=by omega
      have hp1 : p.1=n:=by omega
      exact hpn (Prod.ext hp1 hp0)
    rw [hU p.1 hx,zero_mul]
  · intro hn
    exact (hn (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by simp))).elim
lemma adjoint_sub (F X Y : PowerSeries A) : adjoint F (X-Y)=adjoint F X-adjoint F Y := by
  simp only [adjoint,mul_sub,sub_mul]
lemma adjoint_leading (F X Y : PowerSeries A) (hF : constantCoeff F=1) (n : ℕ)
    (hXY : ∀j<n,coeff j X=coeff j Y) :
    coeff n (adjoint F X)-coeff n (adjoint F Y)=coeff n X-coeff n Y := by
  have hU : ∀j<n,coeff j (X-Y)=0:=by intro j hj; rw [map_sub,hXY j hj,sub_self]
  have hFU : ∀j<n,coeff j (F*(X-Y))=0:=by
    intro j hj
    rw [coeff_mul_vanish_right F _ j (fun k hk=>hU k (hk.trans hj)),hU j hj,mul_zero]
  rw [←map_sub,←adjoint_sub,adjoint,coeff_mul_vanish_left _ _ n hFU,
    coeff_mul_vanish_right F _ n hU,hF,one_mul,constantCoeff_invOfUnit]
  simp only [inv_one,Units.val_one,mul_one,map_sub]
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

local instance instAddGroupTorusLaurentSeriesRat_3_rba43ae_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instSubTorusLaurentSeriesRat_3_rba43ae_1 : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
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
local instance homogeneousElementaryExpressionsAddCommMonoid_rba43ae_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
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

local instance elementaryExpressionBoundsRing_rba43ae_1 : Ring (Torus v Ω) := Torus.instRing v Ω
local instance elementaryExpressionBoundsAddCommMonoid_rba43ae_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance elementaryExpressionBoundsAddGroup_rba43ae_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
local instance instAddCommMonoidTorus_1_rba43ae_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_3_rba43ae_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instNonUnitalSemiringTorus_rba43ae_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_rba43ae_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
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
local instance monomialConjugationAddCommMonoid_rba43ae_1 : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance monomialConjugationAddGroup_rba43ae_1 : AddGroup (Torus v Ω) :=
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
local instance instAddCommMonoidTorus_2_rba43ae_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_4_rba43ae_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
local instance latticeHahnAddCommMonoid_rba43ae_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance latticeHahnAddGroup_rba43ae_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
local instance polynomialAdjointCoefficientsAddCommMonoid_rba43ae_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance polynomialAdjointCoefficientsAddGroup_rba43ae_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
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
local instance pureActualCoefficientsAddCommMonoid_rba43ae_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance pureActualCoefficientsAddGroup_rba43ae_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
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
local instance pureActualScalarCoefficientsAddCommMonoid_rba43ae_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance pureActualScalarCoefficientsAddGroup_rba43ae_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance pureActualScalarCoefficientsNonUnitalSemiring_rba43ae_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
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
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_18_rba43ae_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_18_rba43ae_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
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
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instAddCommGroup _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
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
lemma sectionIncoming_graded (n : ℕ) (X : PowerSeries (Torus v Ω)) :
    sectionIncoming v Ω C F b n X∈shiftRootGrade v Ω C b n := by
  intro m hm
  rw [sectionIncoming_apply,ite_eq_right hm]
lemma sectionIncoming_leading (n : ℕ) (X Y : PowerSeries (Torus v Ω))
    (h : ∀k<n,coeff k X=coeff k Y)
    (hX : coeff n X∈shiftRootGrade v Ω C b n)
    (hY : coeff n Y∈shiftRootGrade v Ω C b n) :
    sectionIncoming v Ω C F b n X-sectionIncoming v Ω C F b n Y=coeff n X-coeff n Y := by
  apply Finsupp.ext
  intro m
  rw [torus_sub_apply,torus_sub_apply,sectionIncoming_apply,sectionIncoming_apply]
  by_cases hm : HasRootDegree C n (m-b)
  · rw [ite_eq_left hm,ite_eq_left hm]
    have H:=adjoint_leading (chartNegative v Ω C (incomingCovector Ω m) F).val X Y
      (chartNegative v Ω C (incomingCovector Ω m) F).property.1 n h
    simpa only [torus_sub_apply,sectionValue] using congrArg (fun t : Torus v Ω=>t m) H
  · rw [ite_eq_right hm,ite_eq_right hm,hX m hm,hY m hm]
lemma sectionIncoming_zero (X : PowerSeries (Torus v Ω))
    (hX : coeff 0 X∈shiftRootGrade v Ω C b 0) :
    sectionIncoming v Ω C F b 0 X=coeff 0 X := by
  apply Finsupp.ext
  intro m
  rw [sectionIncoming_apply]
  by_cases hm : HasRootDegree C 0 (m-b)
  · rw [ite_eq_left hm]
    unfold sectionValue
    rw [coeff_zero_eq_constantCoeff,constant_adjoint _ _ (chartNegative v Ω C _ F).property.1]
  · rw [ite_eq_right hm,hX m hm]

lemma sectionSolution_graded (l : ℕ → Torus v Ω)
    (hl : ∀n,l n∈shiftRootGrade v Ω C b n) :
    ShiftGraded v Ω C b (sectionSolution v Ω C F b l) := by
  intro n
  cases n with
  | zero => simpa only [sectionSolution,coeff_mk,sectionSolutionCoefficients] using hl 0
  | succ n =>
    simp only [sectionSolution,coeff_mk,sectionSolutionCoefficients]
    exact (shiftRootGrade v Ω C b (n+1)).sub_mem (hl _) (sectionIncoming_graded v Ω C F b _ _)
lemma sectionTruncation_lower (l : ℕ → Torus v Ω) (n k : ℕ) (hk : k≤n) :
    coeff k (sectionSolution v Ω C F b l)=coeff k (sectionTruncation v Ω C F b l n) := by
  simp only [sectionSolution,sectionTruncation,coeff_mk,ite_eq_left hk]
lemma sectionTruncation_top (l : ℕ → Torus v Ω) (n : ℕ) :
    coeff (n+1) (sectionTruncation v Ω C F b l n)=0 := by
  simp only [sectionTruncation,coeff_mk,show ¬n+1≤n by omega,ite_false, if_false]
lemma sectionSolution_step (l : ℕ → Torus v Ω) (n : ℕ) :
    coeff (n+1) (sectionSolution v Ω C F b l)=l (n+1)-
      sectionIncoming v Ω C F b (n+1) (sectionTruncation v Ω C F b l n) := by
  simp only [sectionSolution,coeff_mk,sectionSolutionCoefficients,sectionTruncation,dite_eq_ite]
lemma sectionSolution_prescription (l : ℕ → Torus v Ω)
    (hl : ∀n,l n∈shiftRootGrade v Ω C b n) (n : ℕ) :
    sectionIncoming v Ω C F b n (sectionSolution v Ω C F b l)=l n := by
  cases n with
  | zero =>
    rw [sectionIncoming_zero v Ω C F b _ (sectionSolution_graded v Ω C F b l hl 0)]
    simp only [sectionSolution,coeff_mk,sectionSolutionCoefficients]
  | succ n =>
    have ht : coeff (n+1) (sectionTruncation v Ω C F b l n)∈shiftRootGrade v Ω C b (n+1):=by
      rw [sectionTruncation_top]; exact (shiftRootGrade v Ω C b (n+1)).zero_mem
    have H:=sectionIncoming_leading v Ω C F b (n+1)
      (sectionSolution v Ω C F b l) (sectionTruncation v Ω C F b l n)
      (fun k hk=>sectionTruncation_lower v Ω C F b l n k (by omega))
      (sectionSolution_graded v Ω C F b l hl _) ht
    rw [sectionTruncation_top,sub_zero,sectionSolution_step] at H
    exact sub_left_inj.mp H

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
local instance homogenizedPolynomialSectionAddCommMonoid_rba43ae_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance homogenizedPolynomialSectionAddGroup_rba43ae_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance homogenizedPolynomialSectionNonUnitalSemiring_rba43ae_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
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

local instance polynomialSectionRing_rba43ae_1 : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance polynomialSectionAddCommMonoid_rba43ae_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance polynomialSectionAddGroup_rba43ae_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
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

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_ConeSectionDomination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits LaurentPositive
open Classical
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M)
variable (F:CompletedPositive LaurentRay.vUnit Ω C) (base:M)

local instance coneSectionDominationTorusRing_rba43ae_1 : Ring (Torus LaurentRay.vUnit Ω) :=
  Torus.instRing LaurentRay.vUnit Ω
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.coneSectionDominationTorusAddCommMonoid
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.coneSectionDominationTorusAddCommGroup
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.coneSectionDominationTorusAddGroup
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.coneSectionDominationTorusSub
local instance coneSectionDominationTorusNonUnitalSemiring_rba43ae_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) :=
  (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
local instance coneSectionDominationTorusNonUnitalNonAssocSemiring_rba43ae_1 :
    NonUnitalNonAssocSemiring (Torus LaurentRay.vUnit Ω) :=
  (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalNonAssocSemiring
lemma coneDelta_graded (d:ℕ) (m:M) (hm:HasRootDegree C d (m-base)) (k:ℕ) :
    coneDelta Ω d m k ∈ shiftRootGrade LaurentRay.vUnit Ω C base k := by
  by_cases hk:k=d
  · subst k
    intro a ha
    change (if d=d then Torus.X LaurentRay.vUnit Ω m else 0) a=0
    rw [ite_eq_left rfl]
    exact Finsupp.single_eq_of_ne (by intro h; subst a; exact ha hm)
  · rw [coneDelta,ite_eq_right hk]
    exact (shiftRootGrade LaurentRay.vUnit Ω C base k).zero_mem

lemma coneThetaInitial_prescription (d:ℕ) (m:M) (hm:HasRootDegree C d (m-base)) (k:ℕ) :
    sectionIncoming LaurentRay.vUnit Ω C F base k (coneThetaInitial Ω C F base d m)=coneDelta Ω d m k :=
  sectionSolution_prescription _ _ _ _ _ _ (coneDelta_graded Ω C base d m hm) k

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_OrbitMonomialSymmetric
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq _root_.OAI.ElementaryPositivity.TriangularDynamics.instAntisymmCellPhaseLE _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
attribute [-simp] _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.OrbitMonomial
open scoped BigOperators
open Classical
noncomputable section
variable {σ:Type*} [Fintype σ] [DecidableEq σ] {R:Type*} [CommRing R]

lemma exponentOrbit_self (μ:σ →₀ ℕ) : μ∈exponentOrbit μ := by
  refine Finset.mem_image.mpr ⟨Equiv.refl σ,Finset.mem_univ _,?_⟩
  exact Finsupp.mapDomain_id

lemma exponentOrbit_map (μ:σ →₀ ℕ) (e:Equiv.Perm σ) (d:σ →₀ ℕ)
    (hd:d∈exponentOrbit μ) : d.mapDomain e∈exponentOrbit μ := by
  obtain ⟨f,_,rfl⟩:=Finset.mem_image.mp hd
  refine Finset.mem_image.mpr ⟨f.trans e,Finset.mem_univ _,?_⟩
  exact Finsupp.mapDomain_comp (v:=μ) (f:=f) (g:=e)

lemma exponentOrbit_map_iff (μ:σ →₀ ℕ) (e:Equiv.Perm σ) (d:σ →₀ ℕ) :
    d.mapDomain e∈exponentOrbit μ ↔ d∈exponentOrbit μ := by
  constructor
  · intro h
    have H:=exponentOrbit_map μ e.symm _ h
    simpa only [←Finsupp.mapDomain_comp,Equiv.symm_comp_self,Finsupp.mapDomain_id] using H
  · exact exponentOrbit_map μ e d

lemma coeff_polynomial (μ d:σ →₀ ℕ) : (polynomial μ: MvPolynomial σ R).coeff d=
    if d∈exponentOrbit μ then 1 else 0 := by
  simp [polynomial,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial,eq_comm]

lemma polynomial_symmetric (μ:σ →₀ ℕ) : (polynomial μ:MvPolynomial σ R).IsSymmetric := by
  intro e
  apply MvPolynomial.ext
  intro d
  let d':=d.mapDomain e.symm
  have he:d'.mapDomain e=d:=by
    simp only [d',←Finsupp.mapDomain_comp,Equiv.self_comp_symm,Finsupp.mapDomain_id]
  rw [←he,MvPolynomial.coeff_rename_mapDomain e e.injective,coeff_polynomial,coeff_polynomial]
  simp only [exponentOrbit_map_iff]

lemma polynomial_homogeneous (μ:σ →₀ ℕ) :
    (polynomial μ:MvPolynomial σ R).IsHomogeneous μ.degree := by
  apply MvPolynomial.IsHomogeneous.sum
  intro d hd
  obtain ⟨e,_,rfl⟩:=Finset.mem_image.mp hd
  exact MvPolynomial.isHomogeneous_monomial 1 (Finsupp.degree_mapDomain e μ)

lemma dominant_orbit_unique {n:ℕ} (μ ν:Fin (n+1) →₀ ℕ)
    (hμ:∀i:Fin n,μ i.succ ≤ μ i.castSucc) (hν:∀i:Fin n,ν i.succ ≤ ν i.castSucc)
    (h:ν∈exponentOrbit μ) : ν=μ := by
  obtain ⟨e,_,rfl⟩:=Finset.mem_image.mp h
  have hfun:(fun i=>(μ.mapDomain e) i)=(fun i=>μ (e.symm i)):=by
    funext i
    let a:=e.symm i
    have H:=Finsupp.mapDomain_apply e.injective μ a
    simpa only [a,Equiv.apply_symm_apply] using H
  have hp:(List.ofFn (fun i=>(μ.mapDomain e) i)).Perm (List.ofFn (fun i=>μ i)):=by
    rw [hfun]
    exact Equiv.Perm.ofFn_comp_perm (e.symm : Equiv.Perm _) _
  have H:=List.Perm.eq_of_pairwise' (r:=fun a b:ℕ=>b ≤ a)
    (List.pairwise_ofFn.mpr (fun i j hij=>(Fin.antitone_iff_succ_le.mpr hν) (le_of_lt hij)))
    (List.pairwise_ofFn.mpr (fun i j hij=>(Fin.antitone_iff_succ_le.mpr hμ) (le_of_lt hij))) hp
  exact DFunLike.coe_injective (List.ofFn_injective H)

lemma dominant_coeff {n:ℕ} (μ ν:Fin (n+1) →₀ ℕ)
    (hμ:∀i:Fin n,μ i.succ ≤ μ i.castSucc) (hν:∀i:Fin n,ν i.succ ≤ ν i.castSucc) :
    (polynomial μ:MvPolynomial (Fin (n+1)) R).coeff ν=if ν=μ then 1 else 0 := by
  rw [coeff_polynomial]
  congr 1
  exact propext ⟨dominant_orbit_unique μ ν hμ hν,fun h=>h ▸ exponentOrbit_self μ⟩
end
end ElementaryPositivity.OrbitMonomial

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_OrdinaryElementaryExpressions
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

variable {σ : Type*} [Fintype σ] {R : Type*} [CommRing R]

lemma elementary_isHomogeneous (k:ℕ) : (MvPolynomial.esymm σ R k).IsHomogeneous k := by
  unfold MvPolynomial.esymm
  apply MvPolynomial.IsHomogeneous.sum
  intro s hs
  have hc:s.card=k:=(Finset.mem_powersetCard_univ.mp hs)
  simpa [hc] using MvPolynomial.IsHomogeneous.prod s (fun a:σ=>MvPolynomial.X (R:=R) a)
    (fun _=>1) (fun a _=>MvPolynomial.isHomogeneous_X R a)

lemma ElementaryExpr.ordinary_homogeneous {N:ℕ} (f:ElementaryExpr N) :
    (f.ordinary (σ:=σ) (R:=R)).IsHomogeneous N := by
  induction f with
  | zero N => exact MvPolynomial.isHomogeneous_zero σ R N
  | one => exact MvPolynomial.isHomogeneous_one σ R
  | atom k => exact elementary_isHomogeneous k
  | add f g hf hg=>exact hf.add hg
  | neg f hf=>exact hf.neg
  | mul f g hf hg=>exact hf.mul hg

lemma ElementaryExpr.ordinary_cast {N K:ℕ} (h:N=K) (f:ElementaryExpr N) :
    (h ▸ f).ordinary (σ:=σ) (R:=R)=f.ordinary := by subst K; rfl

lemma ElementaryExpr.ordinary_natural (k:ℕ) :
    (ElementaryExpr.natural k).ordinary (σ:=σ) (R:=R)=MvPolynomial.C (k:R) := by
  induction k with
  | zero=>simp [natural,ordinary]
  | succ k ih=>simp [natural,ordinary,ih,Nat.cast_add,Nat.cast_one]

lemma ElementaryExpr.ordinary_integer (z:ℤ) :
    (ElementaryExpr.integer z).ordinary (σ:=σ) (R:=R)=MvPolynomial.C (z:R) := by
  cases z with
  | ofNat k=>simpa [integer] using ordinary_natural (σ:=σ) (R:=R) k
  | negSucc k=>simp [integer,ordinary,ordinary_natural,Int.cast_negSucc]

lemma ElementaryExpr.exists_power {k:ℕ} (f:ElementaryExpr k) (e:ℕ) :
    ∃g:ElementaryExpr (k*e),g.ordinary (σ:=σ) (R:=R)=f.ordinary^e := by
  induction e with
  | zero=>exact ⟨.one,rfl⟩
  | succ e ih=>
    obtain ⟨g,hg⟩:=ih
    rw [Nat.mul_succ]
    refine ⟨.mul g f,?_⟩
    change g.ordinary*f.ordinary=f.ordinary^(e+1)
    rw [hg,pow_succ]

lemma ElementaryExpr.exists_product {ι:Type*} (s:Finset ι) (k:ι → ℕ)
    (f:∀a,ElementaryExpr (k a)) :
    ∃g:ElementaryExpr (∑a∈s,k a),g.ordinary (σ:=σ) (R:=R)=∏a∈s,(f a).ordinary := by
  induction s using Finset.induction with
  | empty=>exact ⟨.one,rfl⟩
  | @insert a s ha ih=>
    obtain ⟨g,hg⟩:=ih
    rw [Finset.sum_insert ha,Finset.prod_insert ha]
    refine ⟨.mul (f a) g,?_⟩
    change (f a).ordinary*g.ordinary=_
    rw [hg]

lemma homogeneousExpression_representation {N:ℕ} (p:MvPolynomial σ ℤ)
    (hp:p.IsSymmetric) (hN:p.IsHomogeneous N) :
    ∃f:ElementaryExpr N,f.ordinary=p := by
  let m:=Fintype.card σ
  obtain ⟨q,hq⟩:=MvPolynomial.esymmAlgHom_surjective (σ:=σ) ℤ (n:=m) le_rfl ⟨p,hp⟩
  let E:=MvPolynomial.esymmAlgHom σ ℤ m
  have he:∀d:Fin m →₀ ℕ,∀z:ℤ,∃K,∃f:ElementaryExpr K,
      f.ordinary=(E (MvPolynomial.monomial d z):MvPolynomial σ ℤ):=by
    intro d z
    choose g hg using fun a:Fin m=>ElementaryExpr.exists_power (σ:=σ) (R:=ℤ) (.atom (a.val+1)) (d a)
    obtain ⟨f,hf⟩:=ElementaryExpr.exists_product (σ:=σ) (R:=ℤ) Finset.univ
      (fun a:Fin m=>(a.val+1)*d a) g
    refine ⟨_,.mul (.integer z) f,?_⟩
    change ((ElementaryExpr.integer z).ordinary)*f.ordinary=_
    rw [ElementaryExpr.ordinary_integer,hf]
    simp only [hg,ElementaryExpr.ordinary]
    simp [E,MvPolynomial.esymmAlgHom,MvPolynomial.aeval_monomial,Finsupp.prod_fintype]
  have hterm:∀d:Fin m →₀ ℕ,∃f:ElementaryExpr N,f.ordinary=
      MvPolynomial.homogeneousComponent N (E (MvPolynomial.monomial d (q.coeff d)):MvPolynomial σ ℤ):=by
    intro d
    obtain ⟨K,f,hf⟩:=he d (q.coeff d)
    rw [←hf,MvPolynomial.homogeneousComponent_of_mem f.ordinary_homogeneous]
    by_cases h:N=K
    · refine ⟨h.symm ▸ f,?_⟩
      simp only [h,ite_true, if_true,ElementaryExpr.ordinary_cast]
    · exact ⟨.zero N,by simp [h,ElementaryExpr.ordinary]⟩
  have hs:∀s:Finset (Fin m →₀ ℕ),∃f:ElementaryExpr N,f.ordinary=
      ∑d∈s,MvPolynomial.homogeneousComponent N (E (MvPolynomial.monomial d (q.coeff d)):MvPolynomial σ ℤ):=by
    intro s
    induction s using Finset.induction with
    | empty=>exact ⟨.zero N,by simp [ElementaryExpr.ordinary]⟩
    | @insert d s hd ih=>
      obtain ⟨f,hf⟩:=hterm d
      obtain ⟨g,hg⟩:=ih
      exact ⟨.add f g,by simp [ElementaryExpr.ordinary,hf,hg,Finset.sum_insert hd]⟩
  obtain ⟨f,hf⟩:=hs q.support
  refine ⟨f,?_⟩
  rw [←map_sum] at hf
  have H:(∑d∈q.support,(E (MvPolynomial.monomial d (q.coeff d)):MvPolynomial σ ℤ))=p:=by
    let E' : MvPolynomial (Fin m) ℤ →ₐ[ℤ] MvPolynomial σ ℤ :=
      (MvPolynomial.symmetricSubalgebra σ ℤ).val.comp E
    change (∑d∈q.support,E' (MvPolynomial.monomial d (q.coeff d)))=p
    rw [←map_sum,←MvPolynomial.as_sum]
    exact congrArg Subtype.val hq
  rw [H,MvPolynomial.homogeneousComponent_eq_self hN] at hf
  exact hf
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_OrdinaryExpressionNaturality
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
variable {σ:Type*} [Fintype σ] {R S:Type*} [CommRing R] [CommRing S]
lemma ElementaryExpr.ordinary_map {N:ℕ} (f:ElementaryExpr N) (φ:R →+* S) :
    MvPolynomial.map φ (f.ordinary (σ:=σ) (R:=R))=f.ordinary (σ:=σ) (R:=S) := by
  induction f with
  | zero=>exact map_zero _
  | one=>exact map_one _
  | atom k=>simp [ordinary,MvPolynomial.esymm]
  | add f g hf hg=>simp only [ordinary,map_add,hf,hg]
  | neg f hf=>simp only [ordinary,map_neg,hf]
  | mul f g hf hg=>simp only [ordinary,map_mul,hf,hg]
end
end ElementaryPositivity.QuantumTorus
namespace ElementaryPositivity.OrbitMonomial
open scoped BigOperators
open Classical
noncomputable section
variable {σ:Type*} [Fintype σ] [DecidableEq σ] {R S:Type*} [CommRing R] [CommRing S]
lemma polynomial_map (μ:σ →₀ ℕ) (φ:R →+* S) :
    MvPolynomial.map φ (polynomial μ:MvPolynomial σ R)=(polynomial μ:MvPolynomial σ S) := by
  simp only [polynomial,map_sum,MvPolynomial.map_monomial,map_one]
end
end ElementaryPositivity.OrbitMonomial

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
local instance instAddCommMonoidTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega_2_rba43ae_1 : AddCommMonoid (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommMonoid
local instance instAddCommGroupTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega_2_rba43ae_1 : AddCommGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommGroup
local instance instAddGroupTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega_2_rba43ae_1 : AddGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddGroup
local instance instSubTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega_2_rba43ae_1 : Sub (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toSub
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
local instance triangularAnchorProjectionSub_rba43ae_1 : Sub (Torus LaurentRay.vUnit (extendedOmega n)) :=
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
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularMonomialProducer
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

lemma orbitExpression_pureCoeff {N:ℕ} (f:ElementaryExpr N) (μ:Fin (n+1) →₀ ℕ)
    (hμ:∀i:Fin n,μ i.succ ≤ μ i.castSucc)
    (hf:f.ordinary= (OrbitMonomial.polynomial μ:MvPolynomial (Fin (n+1)) ℤ))
    (ν:Fin (n+1) → ℤ) (hν:∀i:Fin n,ν i.succ ≤ ν i.castSucc) :
    triangularExpression f (includeVertices (pureAnchor ν))=if ν=(fun a=>(μ a:ℤ)) then 1 else 0 := by
  have hmap:f.ordinary=(OrbitMonomial.polynomial μ:MvPolynomial (Fin (n+1)) (LaurentSeries ℚ)):=by
    rw [←ElementaryExpr.ordinary_map f (Int.castRingHom (LaurentSeries ℚ)),hf,OrbitMonomial.polynomial_map]
  by_cases hnon:∀a,0 ≤ ν a
  · let d:Fin (n+1) →₀ ℕ:=Finsupp.equivFunOnFinite.symm (fun a=>(ν a).toNat)
    have hd:∀a,(d a:ℤ)=ν a:=fun a=>Int.toNat_of_nonneg (hnon a)
    have hdd:∀i:Fin n,d i.succ ≤ d i.castSucc:=by
      intro i
      exact Int.ofNat_le.mp (by simpa only [hd] using hν i)
    have he:includeVertices (pureAnchor ν)=anchorExponent d:=by
      change includeVertices (pureAnchor ν)=includeVertices (pureAnchor (fun a=>(d a:ℤ)))
      rw [show (fun a=>(d a:ℤ))=ν from funext hd]
    rw [he,triangularExpression_anchorCoeff,hmap,OrbitMonomial.dominant_coeff μ d hμ hdd]
    have hh:d=μ ↔ ν=(fun a=>(μ a:ℤ)):=by
      constructor
      · intro h; funext a; rw [←hd a,h]
      · intro h; ext a; apply Int.ofNat_inj.mp; rw [hd,h]
    simp only [hh]
  · obtain ⟨a,ha⟩:=not_forall.mp hnon
    have he:ν≠(fun a=>(μ a:ℤ)):=by intro h; apply ha; rw [h]; exact Int.natCast_nonneg _
    rw [ite_eq_right he]
    by_contra hh
    have H:=triangularSeed_nonneg f _ (Finsupp.mem_support_iff.mpr hh) (.inl a)
    have H':0 ≤ pureAnchor ν (.inl a):=H
    exact ha (by simpa only [pureAnchor_apply_anchor] using H')

lemma natAnchor_rootDegree (μ:Fin (n+1) →₀ ℕ) :
    ∃d,HasRootDegree (extendedRoots n) d (anchorExponent μ-triangularBase μ.degree) := by
  have hpos:∀a,0 ≤ natAnchor (fun a=>μ a) a:=by
    intro a
    cases a <;> simp [natAnchor,pureAnchor_apply_anchor,pureAnchor_apply_bridge]
  obtain ⟨d,c,hc,he⟩:=triangularVertex_rootDegree (natAnchor (fun a=>μ a)) hpos
  have hw:vertexWeight (natAnchor (fun a=>μ a))=(μ.degree:ℤ):=by
    rw [vertexWeight_apply,Fintype.sum_sum_type]
    simp only [natAnchor,pureAnchor_apply_anchor,pureAnchor_apply_bridge,Finset.sum_const_zero,add_zero]
    rw [Finsupp.degree_eq_sum,Nat.cast_sum]
  refine ⟨d,c,hc,?_⟩
  change includeVertices (forwardRoots (fun i=>(c i:ℤ)))=anchorExponent μ-triangularBase μ.degree
  change forwardRoots (fun i=>(c i:ℤ))=natAnchor (fun a=>μ a)-vertexWeight (natAnchor (fun a=>μ a)) • anchor 0 at he
  rw [hw] at he
  rw [he,map_sub]
  rfl

lemma triangularMonomial_producer (μ:Fin (n+1) →₀ ℕ)
    (hμ:∀i:Fin n,μ i.succ ≤ μ i.castSucc) :
    ∃f:ElementaryExpr μ.degree, f.ordinary=(OrbitMonomial.polynomial μ:MvPolynomial (Fin (n+1)) ℤ) ∧
    ∃d,HasRootDegree (extendedRoots n) d (anchorExponent μ-triangularBase μ.degree) ∧
      polynomialInitial (extendedOmega n) (extendedRoots n) (extendedCoord n) (triangularExpression f)=
        coneThetaInitial (extendedOmega n) (extendedRoots n) (simpleTotalTransport (extendedOmega n) (extendedRoots n))
          (triangularBase μ.degree) d (anchorExponent μ) := by
  obtain ⟨f,hf⟩:=homogeneousExpression_representation (OrbitMonomial.polynomial μ:MvPolynomial (Fin (n+1)) ℤ)
    (OrbitMonomial.polynomial_symmetric μ) (OrbitMonomial.polynomial_homogeneous μ)
  obtain ⟨d,hd⟩:=natAnchor_rootDegree μ
  refine ⟨f,hf,d,hd,?_⟩
  exact triangularMonomial_initial f d (fun a=>μ a) (Finsupp.degree_eq_sum μ).symm hμ hd
    (orbitExpression_pureCoeff f μ hμ hf)
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularAnchored
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
variable {n : ℕ}

lemma monomial_producer_supported_oai (μ : Fin (n+1) →₀ ℕ)
    (hμ:∀i:Fin n, μ i.succ ≤ μ i.castSucc) :
    ∃ f:ElementaryExpr μ.degree,
      f.ordinary=(OrbitMonomial.polynomial μ : MvPolynomial (Fin (n+1)) ℤ) ∧
      AnchorSupported (n:=n) f := by
  obtain ⟨f,hf,d,hd,he⟩:=triangularMonomial_producer μ hμ
  refine ⟨f,hf,?_⟩
  intro m hm
  obtain ⟨c,hc⟩:=triangularIncoming_in_rootCone f m hm
  let k:=∑i,c i
  have hk:HasRootDegree (extendedRoots n) k (includeVertices m-triangularBase μ.degree):=by
    refine ⟨c,rfl,?_⟩
    change includeVertices (forwardRoots (fun i=>(c i:ℤ)))=includeVertices m-includeVertices ((μ.degree:ℤ) • anchor 0)
    rw [hc,map_add,add_sub_cancel_left]
  have H := polynomialInitial_incoming (extendedOmega n) extendedOmega_self (extendedRoots n)
    (extendedCoord n) extendedCoord_roots (triangularBase μ.degree) (triangularBase_order μ.degree)
    (triangularExpression f) (by intro a ha; exact triangularSeed_in_rootCone f a (Finsupp.mem_support_iff.mpr ha)) k _ hk
  rw [he,coneThetaInitial_prescription _ _ _ _ _ _ hd] at H
  have hlabel:includeVertices m=anchorExponent μ:=by
    by_contra hh
    have hz:coneDelta (extendedOmega n) d (anchorExponent μ) k (includeVertices m)=0:=by
      unfold coneDelta
      split_ifs
      · exact Finsupp.single_eq_of_ne hh
      · rfl
    exact hm (H.symm.trans hz)
  exact ⟨μ,rfl,hμ,congrArg Prod.fst hlabel⟩

end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

theorem solution : type_of% @OAI.ElementaryPositivity.TriangularDynamics.monomial_producer_supported_oai := @OAI.ElementaryPositivity.TriangularDynamics.monomial_producer_supported_oai
