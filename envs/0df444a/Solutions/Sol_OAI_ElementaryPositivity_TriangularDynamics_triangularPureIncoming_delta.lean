-- Prove2me | solution 1 for OAI.ElementaryPositivity.TriangularDynamics.triangularPureIncoming_delta
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:56:26.69991+00:00
-- url     : https://prove2.me/submissions/8653bf5d-c70b-4915-a96f-11403d37bedd

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

local instance instAddGroupTorusLaurentSeriesRat_r30d44d_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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

local instance instAddGroupTorusLaurentSeriesRat_3_r30d44d_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instSubTorusLaurentSeriesRat_3_r30d44d_1 : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
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
local instance homogeneousElementaryExpressionsAddCommMonoid_r30d44d_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
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

local instance elementaryExpressionBoundsRing_r30d44d_1 : Ring (Torus v Ω) := Torus.instRing v Ω
local instance elementaryExpressionBoundsAddCommMonoid_r30d44d_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance elementaryExpressionBoundsAddGroup_r30d44d_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
local instance instAddCommMonoidTorus_1_r30d44d_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_3_r30d44d_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instNonUnitalSemiringTorus_r30d44d_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_r30d44d_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
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
local instance monomialConjugationAddCommMonoid_r30d44d_1 : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance monomialConjugationAddGroup_r30d44d_1 : AddGroup (Torus v Ω) :=
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
local instance instAddCommMonoidTorus_2_r30d44d_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_4_r30d44d_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
local instance instAddGroupTorus_6_r30d44d_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
local instance latticeHahnAddCommMonoid_r30d44d_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance latticeHahnAddGroup_r30d44d_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
local instance polynomialAdjointCoefficientsAddCommMonoid_r30d44d_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance polynomialAdjointCoefficientsAddGroup_r30d44d_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
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
local instance pureActualCoefficientsAddCommMonoid_r30d44d_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance pureActualCoefficientsAddGroup_r30d44d_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
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
local instance pureActualScalarCoefficientsAddCommMonoid_r30d44d_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance pureActualScalarCoefficientsAddGroup_r30d44d_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance pureActualScalarCoefficientsNonUnitalSemiring_r30d44d_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
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
local instance halfspacePolynomialCoefficientsCoeffAddCommMonoid_r30d44d_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance halfspacePolynomialCoefficientsCoeffAddGroup_r30d44d_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance halfspacePolynomialCoefficientsCoeffNonUnitalSemiring_r30d44d_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
local instance halfspacePolynomialCoefficientsCoeffNonUnitalNonAssocSemiring_r30d44d_1 : NonUnitalNonAssocSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalNonAssocSemiring
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
local instance rootSectionHalfspaceAddCommMonoid_r30d44d_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance rootSectionHalfspaceAddGroup_r30d44d_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
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
local instance targetCyclicAddGroup_r30d44d_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularGapOrthogonality
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
local instance incomingExtremalLocalityTorusAddCommMonoid_r30d44d_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) :=
  (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance incomingExtremalLocalityTorusAddGroup_r30d44d_1 : AddGroup (Torus LaurentRay.vUnit Ω) :=
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
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_LaurentPositiveDomination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension
open Classical
noncomputable section
variable {n:ℕ}

lemma stationary_pure_dominant (μ:Fin (n+1) → ℤ)
    (hxi:∀b:Cell n,0 ≤ triangularOmega n (eventRoot cellLevel 0 b) (pureAnchor μ)) :
    ∀i:Fin n,μ i.succ ≤ μ i.castSucc := by
  intro i
  let b:Cell n:=⟨i,⟨0,by omega⟩⟩
  have H:=hxi b
  simp only [eventRoot,Nat.cast_zero,zero_smul,add_zero,map_sub,AddMonoidHom.sub_apply,
    bridge_pair_pure,anchor_pair_pure,sub_zero] at H
  change 0 ≤ μ i.castSucc-μ i.succ at H
  omega

lemma triangularPureIncoming_dominant {N:ℕ} (f:ElementaryExpr N) (μ:Fin (n+1) → ℤ)
    (h:triangularIncoming f (pureAnchor μ)≠0) : ∀i:Fin n,μ i.succ ≤ μ i.castSucc :=
  stationary_pure_dominant μ (triangularExpression_stationary f (pureAnchor μ) h).2.1

lemma triangularPureIncoming_delta_oai {N:ℕ} (f:ElementaryExpr N) (μ:Fin (n+1) → ℤ)
    (hμ:∀i:Fin n,μ i.succ ≤ μ i.castSucc)
    (hp:∀ν:Fin (n+1) → ℤ,(∀i:Fin n,ν i.succ ≤ ν i.castSucc) →
      triangularExpression f (includeVertices (pureAnchor ν))=if ν=μ then 1 else 0)
    (ν:Fin (n+1) → ℤ) :
    triangularIncoming f (pureAnchor ν)=if ν=μ then 1 else 0 := by
  by_cases hd:∀i:Fin n,ν i.succ ≤ ν i.castSucc
  · rw [triangularPure_incoming f ν hd,hp ν hd]
  · have hne:ν≠μ:=by intro h; subst ν; exact hd hμ
    rw [ite_eq_right hne]
    by_contra hh
    exact hd (triangularPureIncoming_dominant f ν hh)
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

theorem solution : type_of% @OAI.ElementaryPositivity.TriangularDynamics.triangularPureIncoming_delta_oai := @OAI.ElementaryPositivity.TriangularDynamics.triangularPureIncoming_delta_oai
