-- Prove2me | solution 1 for OAI.ElementaryPositivity.TriangularDynamics.triangularLinear_anchorIncoming
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T19:01:18.43661+00:00
-- url     : https://prove2.me/submissions/37b69fbb-b06e-41e7-998e-b7ce88ae519b

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

local instance instAddGroupTorusLaurentSeriesRat_raa4b06_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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

local instance instAddGroupTorusLaurentSeriesRat_3_raa4b06_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instSubTorusLaurentSeriesRat_3_raa4b06_1 : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
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
local instance homogeneousElementaryExpressionsAddCommMonoid_raa4b06_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
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

local instance elementaryExpressionBoundsRing_raa4b06_1 : Ring (Torus v Ω) := Torus.instRing v Ω
local instance elementaryExpressionBoundsAddCommMonoid_raa4b06_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance elementaryExpressionBoundsAddGroup_raa4b06_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
local instance instAddCommMonoidTorus_1_raa4b06_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_3_raa4b06_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instNonUnitalSemiringTorus_raa4b06_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_raa4b06_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
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
local instance monomialConjugationAddCommMonoid_raa4b06_1 : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance monomialConjugationAddGroup_raa4b06_1 : AddGroup (Torus v Ω) :=
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
local instance instAddCommMonoidTorus_2_raa4b06_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_4_raa4b06_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
local instance latticeHahnAddCommMonoid_raa4b06_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance latticeHahnAddGroup_raa4b06_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
local instance polynomialAdjointCoefficientsAddCommMonoid_raa4b06_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance polynomialAdjointCoefficientsAddGroup_raa4b06_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
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
local instance pureActualCoefficientsAddCommMonoid_raa4b06_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance pureActualCoefficientsAddGroup_raa4b06_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
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
local instance pureActualScalarCoefficientsAddCommMonoid_raa4b06_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance pureActualScalarCoefficientsAddGroup_raa4b06_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance pureActualScalarCoefficientsNonUnitalSemiring_raa4b06_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
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
local instance halfspacePolynomialCoefficientsCoeffAddCommMonoid_raa4b06_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance halfspacePolynomialCoefficientsCoeffAddGroup_raa4b06_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance halfspacePolynomialCoefficientsCoeffNonUnitalSemiring_raa4b06_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
local instance halfspacePolynomialCoefficientsCoeffNonUnitalNonAssocSemiring_raa4b06_1 : NonUnitalNonAssocSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalNonAssocSemiring
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
local instance targetCyclicAddGroup_raa4b06_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
local instance rootCoefficientLocalityAddCommMonoid_raa4b06_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) :=
  (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance rootCoefficientLocalityAddGroup_raa4b06_1 : AddGroup (Torus LaurentRay.vUnit Ω) :=
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

lemma vertex_single_injective : Function.Injective (fun a:Vertex n (Cell n)=>
    includeVertices (Pi.single a (1:ℤ))) := by
  intro a b hab
  by_contra h
  have H:=congrArg (fun m:Extended (Vertex n (Cell n))=>m.1 a) hab
  change (Pi.single a (1:ℤ):Lattice n (Cell n)) a=(Pi.single b (1:ℤ):Lattice n (Cell n)) a at H
  simp only [Pi.single_eq_same,Pi.single_eq_of_ne h] at H
  omega

lemma triangularLinear_vertex (a:Vertex n (Cell n)) :
    triangularExpression (.atom 1) (includeVertices (Pi.single a (1:ℤ)))=1 := by
  rw [triangularLinear_sum,Finsupp.finsetSum_apply,Finset.sum_eq_single a]
  · simp [Torus.X,Torus.monomial]
  · intro b _ hba
    apply Finsupp.single_eq_of_ne
    intro hh
    exact hba (vertex_single_injective hh.symm)
  · simp

lemma triangularLinear_anchorIncoming_oai : triangularIncoming (n:=n) (.atom 1) (anchor 0)=1 := by
  have H:=actualPolynomialAdjoint_locality (extendedOmega n) extendedOmega_self
    (extendedRoots n) (extendedCoord n) extendedCoord_roots
    (rootSectionChart (extendedOmega n) (extendedRoots n) (incomingCovector (extendedOmega n) (includeVertices (anchor 0))))
    (includeVertices (anchor 0)) (includeVertices (anchor 0)) (fun _=>0) (by
      change _ = _ + extendedRoots n 0
      rw [map_zero,add_zero])
    (triangularExpression (.atom 1)) (by
      intro b hb
      simpa only [Nat.cast_one,one_smul] using triangularSeed_in_rootCone (.atom 1) b hb)
    (by intro g hg; omega)
  change triangularIncoming (.atom 1) (anchor 0)=_ at H
  rw [H]
  exact triangularLinear_vertex (.inl 0)

end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

theorem solution : type_of% @OAI.ElementaryPositivity.TriangularDynamics.triangularLinear_anchorIncoming_oai := @OAI.ElementaryPositivity.TriangularDynamics.triangularLinear_anchorIncoming_oai
