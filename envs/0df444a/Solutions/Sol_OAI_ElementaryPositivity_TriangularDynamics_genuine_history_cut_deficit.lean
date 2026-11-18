-- Prove2me | solution 1 for OAI.ElementaryPositivity.TriangularDynamics.genuine_history_cut_deficit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:56:24.106494+00:00
-- url     : https://prove2.me/submissions/f135e02b-3c06-404a-9f6c-e482e534e2a8

import Mathlib
import Definitions.Def_OAIQ368Chrom013
import Definitions.Def_OAIQ368Chrom057
import Theorems.Thm_OAI_ElementaryPositivity_QuantumTorus_polynomialSectionIncoming_mutation

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_TorusContinuity
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instAddCommGroup _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
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

local instance instAddGroupTorusLaurentSeriesRat_r398ce1_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instSubTorusLaurentSeriesRat_r398ce1_1 : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
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

local instance instAddGroupTorusLaurentSeriesRat_3_r398ce1_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instSubTorusLaurentSeriesRat_3_r398ce1_1 : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
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
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RationalPureCocycle
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.RationalFiber.pureAction_monomial _root_.OAI.ElementaryPositivity.RationalFiber.scaleAction_coefficientUnit _root_.OAI.ElementaryPositivity.RationalFiber.scaleAction_variableUnit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
noncomputable section
variable {K : Type*} [Field K]

lemma pureRatio_nat (v : Kˣ) (n : ℕ) :
    pureRatio v (n:ℤ)=∏i∈Finset.range n,scaleAction v (Multiplicative.ofAdd (i:ℤ)) (pureStep v) := by
  induction n with
  | zero=>simp
  | succ n ih=>rw [Nat.cast_add,Nat.cast_one,pureRatio_add,pureRatio_one,ih,Finset.prod_range_succ]
lemma pureRatio_nat_val (v : Kˣ) (n : ℕ) :
    (pureRatio v (n:ℤ):RatFunc K)=
      ∏i∈Finset.range n,(1+RatFunc.C (↑(v^(-2*(i:ℤ)-1)):K)*RatFunc.X) := by
  rw [pureRatio_nat,Units.coe_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [scaleAction_val]
  change scale (v^(-2*(i:ℤ))) (1+RatFunc.C (↑(v⁻¹):K)*RatFunc.X)=_
  rw [map_add,map_one,map_mul,scale_constant,scale_X,←mul_assoc,←map_mul,
    ←Units.val_mul,←zpow_neg_one,←zpow_add]
  congr 3
  ring_nf
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RationalCutIdentity
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.WallUnits
open Polynomial
noncomputable section
variable {K : Type*} [Field K]
lemma natDegree_linear_le (a : K) : (1+C a*X).natDegree≤1 := by
  exact natDegree_add_le_of_degree_le (by simp) ((natDegree_C_mul_le _ _).trans (natDegree_X_le))
end
end ElementaryPositivity.WallUnits

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RealRootCoordinates
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (C : (I → ℤ) →+ M) (e : M →+ E)

lemma covector_root_eval (h:Module.Dual ℝ E) (hh:∀i,h (e (simpleRoot C i))=1)
    {n:ℕ} {m:M} (hm:HasRootDegree C n m) : h (e m)=(n:ℝ) := by
  obtain ⟨a,ha,rfl⟩:=hm
  rw [coefficient_simple_expansion C,map_sum,map_sum]
  simp only [map_zsmul,hh,zsmul_eq_mul,mul_one]
  exact_mod_cast ha

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_IndependentSetElements
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instAddCommGroup _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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
variable {K M V W : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ)

lemma independent_sum_iff (hΩ : ∀m,Ω m m=0) (u : V → M) (w : W → M)
    (s : Finset V) (t : Finset W) :
    IsIndependent Ω (Sum.elim u w) (s.disjSum t) ↔
      IsIndependent Ω u s ∧ IsIndependent Ω w t ∧
        ∀x∈s,∀y∈t,Ω (u x) (w y)=0 := by
  constructor
  · intro h
    refine ⟨?_,?_,?_⟩
    · intro x hx y hy
      exact h (.inl x) (by simpa) (.inl y) (by simpa)
    · intro x hx y hy
      exact h (.inr x) (by simpa) (.inr y) (by simpa)
    · intro x hx y hy
      exact h (.inl x) (by simpa) (.inr y) (by simpa)
  · rintro ⟨hs,ht,hst⟩ x hx y hy
    cases x with
    | inl x =>
      cases y with
      | inl y => exact hs x (by simpa using hx) y (by simpa using hy)
      | inr y => exact hst x (by simpa using hx) y (by simpa using hy)
    | inr x =>
      cases y with
      | inl y =>
        have H:=alternating_skew Ω hΩ (w x) (u y)
        rw [hst y (by simpa using hy) x (by simpa using hx)] at H
        simpa using H
      | inr y => exact ht x (by simpa using hx) y (by simpa using hy)

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
section
namespace ElementaryPositivity.QuantumTorus
open scoped BigOperators
open Classical
noncomputable section
variable {K M W : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ)

lemma compatible_add (a b : M) (w : W → M) (t : Finset W)
    (hb : Compatible Ω b w t) : Compatible Ω (a+b) w t ↔ Compatible Ω a w t := by
  unfold Compatible at *
  simp only [map_add,AddMonoidHom.add_apply]
  constructor <;> intro h y hy
  · have H:=h y hy
    simpa only [hb y hy,add_zero] using H
  · simpa only [hb y hy,add_zero] using h y hy

lemma finset_fin_three : (Finset.univ : Finset (Finset (Fin 3))) =
    {∅,{0},{1},{2},{0,1},{0,2},{1,2},{0,1,2}} := by decide

lemma independent_triple_sum [DecidableEq W]
    (hΩ : ∀m,Ω m m=0) (a b c : M)
    (hab : Ω a b≠0) (hbc : Ω b c≠0) (hac : Ω a c=0)
    (w : W → M) (t : Finset W) (k : ℕ) :
    (∑ s : Finset (Fin 3),
      independentTerm v Ω (Sum.elim ![a,b,c] w) k (s.disjSum t)) =
    if IsIndependent Ω w t then
      (if t.card=k then Torus.X v Ω (∑y∈t,w y) else 0) +
      (if t.card+1=k ∧ Compatible Ω a w t then Torus.X v Ω (a+∑y∈t,w y) else 0) +
      (if t.card+1=k ∧ Compatible Ω b w t then Torus.X v Ω (b+∑y∈t,w y) else 0) +
      (if t.card+1=k ∧ Compatible Ω c w t then Torus.X v Ω (c+∑y∈t,w y) else 0) +
      (if t.card+2=k ∧ Compatible Ω a w t ∧ Compatible Ω c w t then
        Torus.X v Ω (a+c+∑y∈t,w y) else 0)
    else 0 := by
  have hca : Ω c a=0 := by rw [alternating_skew Ω hΩ c a,hac,neg_zero]
  rw [finset_fin_three]
  simp (disch := decide) only [Finset.sum_insert,Finset.sum_singleton]
  simp only [independentTerm,independent_sum_iff Ω hΩ,Finset.card_disjSum,
    setMonomial,sum_labels_disjSum]
  by_cases H : IsIndependent Ω w t
  all_goals
    simp only [IsIndependent] at H
    simp [IsIndependent,Compatible,hΩ,hab,hbc,hac,hca,H,
      and_assoc,and_comm,Nat.add_comm,add_assoc]
  simp only [iff_true_intro H,and_true,ite_true, if_true]

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_IndependentElementReindex
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
attribute [-simp] _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open Classical
open scoped BigOperators
noncomputable section
variable {K M V W : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ)

lemma independent_map [DecidableEq V] [DecidableEq W]
    (u : W → M) (e : V ↪ W) (s : Finset V) :
    IsIndependent Ω u (s.map e) ↔ IsIndependent Ω (u∘e) s := by
  simp [IsIndependent]

lemma independentTerm_map [DecidableEq V] [DecidableEq W]
    (u : W → M) (e : V ↪ W) (s : Finset V) (k : ℕ) :
    independentTerm v Ω u k (s.map e)=independentTerm v Ω (u∘e) k s := by
  simp only [independentTerm,independent_map,Finset.card_map,setMonomial,Finset.sum_map]
  rfl

lemma independentElement_reindex [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (u : W → M) (e : V ≃ W) (k : ℕ) :
    independentElement v Ω u k=independentElement v Ω (u∘e) k := by
  unfold independentElement
  rw [←Equiv.sum_comp e.finsetCongr]
  apply Finset.sum_congr rfl
  intro s _
  exact independentTerm_map v Ω u e.toEmbedding s k

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RationalCenteredAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus WallUnits Polynomial
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ)
lemma centeredPolynomial_degree_le (t : ℕ) : (centeredPolynomial v t).natDegree≤t := by
  unfold centeredPolynomial
  have H:=Polynomial.natDegree_prod_le Finset.univ
    (fun i : Fin t=>(1+Polynomial.C (↑(v^centeredExponent t i):K)*Polynomial.X))
  have H' := Finset.sum_le_sum (s:=Finset.univ) (fun (i : Fin t) _ =>
    natDegree_linear_le (↑(v^centeredExponent t i):K))
  exact H.trans (by simpa using H')
lemma centered_eval_ratio (t : ℕ) :
    (centeredPolynomial v t).eval₂ RatFunc.C
      (RatFunc.C (↑(v^(-(t:ℤ))):K)*RatFunc.X)=(pureRatio v (t:ℤ):RatFunc K) := by
  change (Polynomial.eval₂RingHom RatFunc.C
    (RatFunc.C (↑(v^(-(t:ℤ))):K)*RatFunc.X)) (centeredPolynomial v t)=_
  rw [centeredPolynomial,map_prod,pureRatio_nat_val,←Fin.prod_univ_eq_prod_range]
  change (∏i : Fin t, (1+Polynomial.C (↑(v^centeredExponent t i):K)*Polynomial.X).eval₂ RatFunc.C
    (RatFunc.C (↑(v^(-(t:ℤ))):K)*RatFunc.X))=_
  have H (i : Fin t) :
      (1+Polynomial.C (↑(v^centeredExponent t i):K)*Polynomial.X).eval₂ RatFunc.C
        (RatFunc.C (↑(v^(-(t:ℤ))):K)*RatFunc.X)=
      1+RatFunc.C (↑(v^(-2*((i.rev:ℕ):ℤ)-1)):K)*RatFunc.X := by
    simp only [Polynomial.eval₂_add,Polynomial.eval₂_one,Polynomial.eval₂_mul,
      Polynomial.eval₂_C,Polynomial.eval₂_X]
    rw [←mul_assoc,←map_mul,←Units.val_mul,←zpow_add]
    congr 4
    simp only [centeredExponent,Fin.val_rev]
    have H:=i.isLt
    congr 1
    omega
  simp_rw [H]
  exact Equiv.prod_comp Fin.revPerm
    (fun i : Fin t=>1+RatFunc.C (↑(v^(-2*((i:ℕ):ℤ)-1)):K)*RatFunc.X)

variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)
include hΩ in
lemma complement_pairing (m : M) : complementAlpha k p Ω (off k p hp m)=Ω p m := by
  change Ω p (m-k m • p)=_
  rw [map_sub,map_zsmul,hΩ,smul_zero,sub_zero]
lemma centeredScalar_shift (n a j : ℤ) : centeredScalar v (n+j) a=
    centeredScalar v n a*(RatFunc.C (↑(v^(-a)):K)*RatFunc.X)^j := by
  have hz : (RatFunc.X:RatFunc K)≠0:=RatFunc.X_ne_zero
  rw [centeredScalar,centeredScalar,mul_zpow,←map_zpow₀,
    ←Units.val_zpow_eq_zpow_val,←zpow_mul,zpow_add₀ hz]
  rw [show -(n+j)*a= -n*a+(-a)*j by ring,zpow_add,Units.val_mul,map_mul]
  ring
include hΩ in
lemma embed_pure_row_term (m : M) (j : ℕ) (a : K) :
    embed v Ω hΩ k p hp (Torus.monomial v Ω (m+j • p) a)=
      FiberTorus.monomial v _ _ (off k p hp m)
        (centeredScalar v (k m) (Ω p m)*RatFunc.C a*
          (RatFunc.C (↑(v^(-Ω p m)):K)*RatFunc.X)^j) := by
  rw [embed_monomial]
  simp only [map_add,map_nsmul,hp,nsmul_eq_mul,mul_one,off_p,smul_zero,add_zero]
  rw [complement_pairing Ω hΩ k p hp m,centeredScalar_shift]
  rw [zpow_natCast]
  congr 1
  ring
include hΩ in
lemma pureAction_centered (m : M) (t : ℕ) (ht : Ω p m=(t:ℤ)) :
    pureAction v (complementOmega k Ω) (complementAlpha k p Ω)
      (embed v Ω hΩ k p hp (Torus.X v Ω m))=
      embed v Ω hΩ k p hp (centeredCrossing v Ω p m t) := by
  rw [Torus.X,embed_monomial,pureAction_monomial,map_one,one_mul,
    complement_pairing Ω hΩ k p hp m,ht,←centered_eval_ratio]
  rw [centeredCrossing,map_sum]
  simp_rw [embed_pure_row_term v Ω hΩ k p hp,ht]
  have He := Polynomial.eval₂_eq_sum_range' RatFunc.C
    (Nat.lt_succ_of_le (centeredPolynomial_degree_le v t))
    (RatFunc.C (↑(v^(-(t:ℤ))):K)*RatFunc.X)
  rw [He,Finset.mul_sum]
  rw [←Fin.sum_univ_eq_sum_range]
  simp only [FiberTorus.monomial,mul_assoc]
  classical
  exact (map_sum (Finsupp.singleAddHom (off k p hp m)) _ Finset.univ)
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RotationLocalPolynomials
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open WallUnits
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ)

lemma centeredCrossing_zero (p m : M) : centeredCrossing v Ω p m 0 = Torus.X v Ω m := by
  simp [centeredCrossing,centeredPolynomial,Torus.X]

lemma centeredCrossing_one (p m : M) : centeredCrossing v Ω p m 1 =
    Torus.X v Ω m + Torus.X v Ω (m+p) := by
  simp [centeredCrossing,centeredPolynomial,centeredExponent,Fin.sum_univ_two,Torus.X,Polynomial.coeff_one]
end
end ElementaryPositivity.QuantumTorus

namespace ElementaryPositivity.RationalFiber
open QuantumTorus WallUnits
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀ m, Ω m m=0)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)
include hΩ in
lemma pureAction_pairing_zero (m : M) (hm : Ω p m=0) :
    pureAction v (complementOmega k Ω) (complementAlpha k p Ω)
      (embed v Ω hΩ k p hp (Torus.X v Ω m)) =
      embed v Ω hΩ k p hp (Torus.X v Ω m) := by
  simpa only [centeredCrossing_zero] using pureAction_centered v Ω hΩ k p hp m 0 hm

include hΩ in
lemma pureAction_pairing_one (m : M) (hm : Ω p m=1) :
    pureAction v (complementOmega k Ω) (complementAlpha k p Ω)
      (embed v Ω hΩ k p hp (Torus.X v Ω m)) =
      embed v Ω hΩ k p hp (Torus.X v Ω m + Torus.X v Ω (m+p)) := by
  simpa only [centeredCrossing_one] using pureAction_centered v Ω hΩ k p hp m 1 hm

lemma pureRatio_neg_one_cancel : (pureRatio v (-1):RatFunc K) *
    (1+RatFunc.C (v:K)*RatFunc.X)=1 := by
  have H := congrArg (fun a : (RatFunc K)ˣ => (a:RatFunc K)) (pureRatio_add v (-1) 1)
  simp only [neg_add_cancel,pureRatio_zero,Units.val_one,Units.val_mul,scaleAction_val,
    pureRatio_one] at H
  change 1=(pureRatio v (-1):RatFunc K)*
    scale (v^(-2*(-1:ℤ))) (1+RatFunc.C (↑(v⁻¹):K)*RatFunc.X) at H
  have HH : scale (v^(-2*(-1:ℤ))) (1+RatFunc.C (↑(v⁻¹):K)*RatFunc.X)=
      1+RatFunc.C (v:K)*RatFunc.X := by
    rw [map_add,map_one,map_mul,scale_constant,scale_X,←mul_assoc,←map_mul,
      ←Units.val_mul,←zpow_neg_one,←zpow_add]
    norm_num
  rw [HH] at H
  exact H.symm

include hΩ in
lemma pureAction_pairing_neg_one (m : M) (hm : Ω p m= -1) :
    pureAction v (complementOmega k Ω) (complementAlpha k p Ω)
      (embed v Ω hΩ k p hp (Torus.X v Ω m + Torus.X v Ω (m+p))) =
      embed v Ω hΩ k p hp (Torus.X v Ω m) := by
  have H0 := embed_pure_row_term v Ω hΩ k p hp m 0 1
  have H1 := embed_pure_row_term v Ω hΩ k p hp m 1 1
  simp only [zero_smul,add_zero,map_one,mul_one,pow_zero,one_smul,pow_one,hm,
    neg_neg,zpow_one] at H0 H1
  rw [map_add,map_add,Torus.X,Torus.X,H0,H1,pureAction_monomial,pureAction_monomial,
    complement_pairing Ω hΩ k p hp m,hm,←FiberTorus.monomial_add]
  congr 1
  have H := pureRatio_neg_one_cancel v
  calc
    _ = centeredScalar v (k m) (-1) *
        ((pureRatio v (-1):RatFunc K)*(1+RatFunc.C (v:K)*RatFunc.X)) := by ring
    _ = _ := by rw [H,mul_one]
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_IndependentRotationComparison
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus
open scoped BigOperators
open Classical
noncomputable section
variable {K M W : Type*} [Field K] [AddCommGroup M] [DecidableEq W]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (ell : M →+ ℤ) (p : M) (hp : ell p=1)

include hΩ in
lemma independent_rotation_slice (a c : M) (hpa : Ω p a=1) (hpc : Ω p c= -1)
    (hac : Ω a c=0) (w : W → M) (hw : ∀y,Ω p (w y)=0)
    (t : Finset W) (k : ℕ) :
    pureAction v (complementOmega ell Ω) (complementAlpha ell p Ω)
      (embed v Ω hΩ ell p hp (∑ s : Finset (Fin 3),
        independentTerm v Ω (Sum.elim ![a,c+p,c] w) k (s.disjSum t))) =
      embed v Ω hΩ ell p hp (∑ s : Finset (Fin 3),
        independentTerm v Ω (Sum.elim ![a,a+p,c] w) k (s.disjSum t)) := by
  have hap : Ω a p= -1 := by rw [alternating_skew Ω hΩ a p,hpa]
  have oldab : Ω a (a+p)≠0 := by simp [map_add,hΩ,hap]
  have oldbc : Ω (a+p) c≠0 := by simp [map_add,hac,hpc]
  have newab : Ω a (c+p)≠0 := by simp [map_add,hac,hap]
  have newbc : Ω (c+p) c≠0 := by simp [map_add,hΩ,hpc]
  have hwp : Compatible Ω p w t := fun y _ => hw y
  have HA := compatible_add Ω a p w t hwp
  have HC := compatible_add Ω c p w t hwp
  rw [independent_triple_sum v Ω hΩ a (c+p) c newab newbc hac,
    independent_triple_sum v Ω hΩ a (a+p) c oldab oldbc hac]
  simp only [HA,HC]
  by_cases ht : IsIndependent Ω w t
  swap
  · simp only [ht,ite_false, if_false,map_zero]
  simp only [ht,ite_true, if_true]
  let z := ∑y∈t,w y
  have hpz : Ω p z=0 := by simp [z,map_sum,hw]
  have hpa' : Ω p (a+z)=1 := by rw [map_add,hpa,hpz,add_zero]
  have hpc' : Ω p (c+z)= -1 := by rw [map_add,hpc,hpz,add_zero]
  have hpac : Ω p (a+c+z)=0 := by rw [map_add,map_add,hpa,hpc,hpz]; norm_num
  have HA' := pureAction_pairing_one v Ω hΩ ell p hp (a+z) hpa'
  have HC' := pureAction_pairing_neg_one v Ω hΩ ell p hp (c+z) hpc'
  have H0 := pureAction_pairing_zero v Ω hΩ ell p hp z hpz
  have HAC := pureAction_pairing_zero v Ω hΩ ell p hp (a+c+z) hpac
  have hza : a+p+z=a+z+p := by abel
  have hzc : c+p+z=c+z+p := by abel
  change pureAction v _ _ (embed v Ω hΩ ell p hp
    ((if t.card=k then Torus.X v Ω z else 0)+
      (if t.card+1=k ∧ Compatible Ω a w t then Torus.X v Ω (a+z) else 0)+
      (if t.card+1=k ∧ Compatible Ω c w t then Torus.X v Ω (c+p+z) else 0)+
      (if t.card+1=k ∧ Compatible Ω c w t then Torus.X v Ω (c+z) else 0)+
      (if t.card+2=k ∧ Compatible Ω a w t ∧ Compatible Ω c w t then Torus.X v Ω (a+c+z) else 0))) = _
  rw [hza,hzc]
  have groupNew (A B C D E : Torus v Ω) : A+B+C+D+E=A+B+(D+C)+E := by abel
  rw [groupNew]
  simp only [ite_add_ite,zero_add]
  have groupOld (A B C D E : Torus v Ω) : A+B+C+D+E=A+(B+C)+D+E := by abel
  conv_rhs => rw [groupOld]
  simp only [ite_add_ite,zero_add]
  simp only [map_add]
  have embite (P : Prop) [Decidable P] (x : Torus v Ω) :
      embed v Ω hΩ ell p hp (if P then x else 0) =
        if P then embed v Ω hΩ ell p hp x else 0 := by
    split_ifs <;> simp
  have actite (P : Prop) [Decidable P] (x) :
      pureAction v (complementOmega ell Ω) (complementAlpha ell p Ω)
        (if P then x else 0) =
        if P then pureAction v (complementOmega ell Ω) (complementAlpha ell p Ω) x else 0 := by
    split_ifs <;> simp
  simp only [embite,actite]
  simp only [H0,HA',HC',HAC]
  rfl

include hΩ in
lemma independentElement_rotation [Fintype W] (a c : M)
    (hpa : Ω p a=1) (hpc : Ω p c= -1) (hac : Ω a c=0)
    (w : W → M) (hw : ∀y,Ω p (w y)=0) (k : ℕ) :
    pureAction v (complementOmega ell Ω) (complementAlpha ell p Ω)
      (embed v Ω hΩ ell p hp (independentElement v Ω (Sum.elim ![a,c+p,c] w) k)) =
      embed v Ω hΩ ell p hp (independentElement v Ω (Sum.elim ![a,a+p,c] w) k) := by
  rw [independent_sum_decomposition,independent_sum_decomposition,map_sum,map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro t _
  exact independent_rotation_slice v Ω hΩ ell p hp a c hpa hpc hac w hw t k
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_NamedIndependentRotation
attribute [-instance] _root_.OAI.ElementaryPositivity.TriangularDynamics.cutContains_decidable
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus
open Classical
noncomputable section
variable {K M V : Type*} [Field K] [AddCommGroup M] [Fintype V] [DecidableEq V]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (ell : M →+ ℤ) (p : M) (hp : ell p=1)

include hΩ in
lemma independentElement_named_rotation (w : V → M) (a b c : V)
    (hab : a≠b) (hbc : b≠c) (hac : a≠c)
    (hwb : w b=w a+p) (hpa : Ω p (w a)=1) (hpc : Ω p (w c)= -1)
    (hac0 : Ω (w a) (w c)=0) (hw : ∀x,x≠a → x≠b → x≠c → Ω p (w x)=0) (k : ℕ) :
    pureAction v (complementOmega ell Ω) (complementAlpha ell p Ω)
      (embed v Ω hΩ ell p hp (independentElement v Ω (Function.update w b (w c+p)) k)) =
      embed v Ω hΩ ell p hp (independentElement v Ω w k) := by
  let e : Fin 3 ↪ V := ⟨![a,b,c],by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩
  let W := {x : V // x∉Set.range e}
  let eqv := embeddingSumCompl e
  let outside : W → M := fun x=>w x.val
  have ho : ∀x:W, x.val≠a ∧ x.val≠b ∧ x.val≠c := by
    intro x
    refine ⟨?_,?_,?_⟩
    · intro h; exact x.property ⟨0,h.symm⟩
    · intro h; exact x.property ⟨1,h.symm⟩
    · intro h; exact x.property ⟨2,h.symm⟩
  have hold : w ∘ eqv=Sum.elim ![w a,w a+p,w c] outside := by
    funext x
    cases x with
    | inl i =>
      change w (![a,b,c] i)=![w a,w a+p,w c] i
      fin_cases i <;> simp [hwb]
    | inr x => rfl
  have hnew : (Function.update w b (w c+p)) ∘ eqv=
      Sum.elim ![w a,w c+p,w c] outside := by
    funext x
    cases x with
    | inl i =>
      change Function.update w b (w c+p) (![a,b,c] i)=![w a,w c+p,w c] i
      fin_cases i <;> simp [hab,Ne.symm hbc]
    | inr x =>
      change Function.update w b (w c+p) x.val=w x.val
      exact Function.update_of_ne (ho x).2.1 _ _
  rw [independentElement_reindex v Ω (Function.update w b (w c+p)) eqv k,
    independentElement_reindex v Ω w eqv k,hnew,hold]
  exact independentElement_rotation v Ω hΩ ell p hp (w a) (w c) hpa hpc hac0 outside
    (fun x=>hw x.val (ho x).1 (ho x).2.1 (ho x).2.2) k
end
end ElementaryPositivity.RationalFiber

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
local instance homogeneousElementaryExpressionsAddCommMonoid_r398ce1_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
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

lemma independentElement_cutSupported (ell:M →+ ℤ) (w:V → M) (hw:∀x,ell (w x)≤1) (k:ℕ) :
    CutSupported v Ω ell k (independentElement v Ω w k) := by
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
      ∑x∈s,ell (w x) ≤ ∑_x∈s,(1:ℤ) := Finset.sum_le_sum fun x _=>hw x
      _ = k := by simp [hc.2]
  · exact (hs rfl).elim

lemma ElementaryExpr.cutSupported {k:ℕ} (f:ElementaryExpr k) (ell:M →+ ℤ)
    (w:V → M) (hw:∀x,ell (w x)≤1) : CutSupported v Ω ell k (f.eval v Ω w) := by
  induction f with
  | zero k => exact cutSupported_zero v Ω ell k
  | one => exact cutSupported_one v Ω ell
  | atom k => exact independentElement_cutSupported v Ω ell w hw k
  | add f g hf hg => exact cutSupported_add v Ω ell _ hf hg
  | neg f hf => exact cutSupported_neg v Ω ell _ hf
  | mul f g hf hg => simpa only [eval,Nat.cast_add] using cutSupported_mul v Ω ell _ _ hf hg

open RationalFiber
lemma ElementaryExpr.rotation (hΩ:∀m,Ω m m=0) (ell:M →+ ℤ) (p:M) (hp:ell p=1)
    (w:V → M) (a b c:V) (hab:a≠b) (hbc:b≠c) (hac:a≠c)
    (hwb:w b=w a+p) (hpa:Ω p (w a)=1) (hpc:Ω p (w c)= -1)
    (hac0:Ω (w a) (w c)=0) (hw:∀x,x≠a → x≠b → x≠c → Ω p (w x)=0)
    {k:ℕ} (f:ElementaryExpr k) :
    pureAction v (complementOmega ell Ω) (complementAlpha ell p Ω)
      (embed v Ω hΩ ell p hp (f.eval v Ω (Function.update w b (w c+p))))=
        embed v Ω hΩ ell p hp (f.eval v Ω w) := by
  induction f with
  | zero k => simp [eval]
  | one => simp [eval]
  | atom k => exact independentElement_named_rotation v Ω hΩ ell p hp w a b c hab hbc hac hwb hpa hpc hac0 hw k
  | add f g hf hg => simp only [eval,map_add,hf,hg]
  | neg f hf => simp only [eval,map_neg,hf]
  | mul f g hf hg => simp only [eval,map_mul,hf,hg]
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
local instance instAddCommMonoidTorus_1_r398ce1_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_3_r398ce1_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instNonUnitalSemiringTorus_r398ce1_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_r398ce1_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
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

end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.TriangularDynamics
open scoped BigOperators

lemma triangularBB_skew {n : ℕ} (b c : Cell n) : triangularBB b c= -triangularBB c b := by
  unfold triangularBB
  ring

end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularScheduledRoots
attribute [-instance] _root_.OAI.ElementaryPositivity.TriangularDynamics.instAntisymmCellPhaseLE _root_.OAI.ElementaryPositivity.TriangularDynamics.instDecidableRelCellPhaseLE _root_.OAI.ElementaryPositivity.TriangularDynamics.instIsTransCellPhaseLE _root_.OAI.ElementaryPositivity.TriangularDynamics.instTotalCellPhaseLE
attribute [-simp] _root_.OAI.ElementaryPositivity.TriangularDynamics.forwardCoord_roots _root_.OAI.ElementaryPositivity.TriangularDynamics.levelNode_last _root_.OAI.ElementaryPositivity.TriangularDynamics.levelNode_zero _root_.OAI.ElementaryPositivity.TriangularDynamics.mem_phaseCycle _root_.OAI.ElementaryPositivity.TriangularDynamics.partialBridge_cycle _root_.OAI.ElementaryPositivity.TriangularDynamics.partialBridge_nil
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

lemma levelCartan_comm (i j : Fin n) : levelCartan i j=levelCartan j i := by
  simp only [levelCartan,eq_comm,or_comm]

lemma omega_delta_bridge (b c : Cell n) :
    triangularOmega n (delta cellLevel b) (bridge c)=levelCartan b.1 c.1 := by
  simp only [delta,map_sub,AddMonoidHom.sub_apply]
  change matrixPairing _ (anchor b.1.succ) (bridge c)-
      matrixPairing _ (anchor b.1.castSucc) (bridge c)=_
  simp only [anchor,bridge,matrixPairing_single,chartMatrix]
  dsimp only [cellLevel]
  simp only [Fin.ext_iff,Fin.val_succ,Fin.val_castSucc,levelCartan]
  split_ifs <;> omega

lemma omega_event_delta (b c : Cell n) :
    triangularOmega n (eventRoot cellLevel 0 b) (delta cellLevel c)= -levelCartan b.1 c.1 := by
  rw [triangularOmega_skew]
  simp only [eventRoot,Nat.cast_zero,zero_smul,add_zero,map_sub,omega_delta_anchor,
    sub_zero,omega_delta_bridge,levelCartan_comm c.1 b.1]

lemma scheduledRoot_anchor (L : ℕ) (b : Cell n) (a : Fin (n+1)) :
    triangularOmega n (eventRoot cellLevel L b) (anchor a)=
      (if a=b.1.castSucc then 1 else 0)-(if a=b.1.succ then 1 else 0) := by
  have he : eventRoot cellLevel L b=eventRoot cellLevel 0 b+(L:ℤ) • delta cellLevel b := by
    simp [eventRoot]
  rw [he,map_add,AddMonoidHom.add_apply,map_zsmul,AddMonoidHom.zsmul_apply,
    omega_delta_anchor,smul_zero,add_zero,eventRoot_anchor]

lemma scheduledRoot_bridge (L : ℕ) (b c : Cell n) :
    triangularOmega n (eventRoot cellLevel L b) (scheduledBridge L b c)=if c=b then 1 else 0 := by
  have he : eventRoot cellLevel L b=eventRoot cellLevel 0 b+(L:ℤ) • delta cellLevel b := by
    simp [eventRoot]
  rw [he,scheduledBridge]
  simp only [map_add,map_zsmul,AddMonoidHom.add_apply,AddMonoidHom.zsmul_apply,
    omega_delta_delta,omega_delta_bridge,omega_event_delta,
    eventRoot_bridge_value,smul_eq_mul]
  by_cases heq : c=b
  · subst c
    simp [levelCartan]
  · by_cases hl : c.1=b.1
    · have hl' := hl.symm
      by_cases hh : phaseEarlier c b
      · simp only [levelCartan,ite_eq_left hl,ite_eq_left hl',ite_eq_right heq]
        simp only [hh,ite_true, if_true]
        ring
      · simp only [levelCartan,ite_eq_left hl,ite_eq_left hl',ite_eq_right heq]
        simp only [hh,ite_false, if_false]
        ring
    · have hl' : b.1≠c.1 := Ne.symm hl
      by_cases ha : c.1.val+1=b.1.val ∨ b.1.val+1=c.1.val
      · have ha' : b.1.val+1=c.1.val ∨ c.1.val+1=b.1.val := ha.symm
        by_cases hh : phaseEarlier c b
        · simp only [levelCartan,ite_eq_right hl,ite_eq_right hl',ite_eq_right heq,ha,ha',hh,ite_true, if_true]
          ring
        · simp only [levelCartan,ite_eq_right hl,ite_eq_right hl',ite_eq_right heq,ha,ha',hh,ite_true, if_true,ite_false, if_false]
          ring
      · have ha' : ¬(b.1.val+1=c.1.val ∨ c.1.val+1=b.1.val) := by tauto
        simp only [levelCartan,ite_eq_right hl,ite_eq_right hl',ite_eq_right heq,ha,ha',ite_false, if_false]
        ring

end ElementaryPositivity.TriangularDynamics

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
open Classical
noncomputable section
variable {n : ℕ}

lemma phaseCycle_nodup : (phaseCycle n).Nodup := Finset.sort_nodup _ _
lemma phaseCycle_pairwise : (phaseCycle n).Pairwise phaseLE := by
  exact Finset.pairwise_sort _ _

lemma prefix_before {pre post : List (Cell n)} {b c : Cell n}
    (hcycle : phaseCycle n=pre++b::post) : c∈pre ↔ phaseEarlier c b := by
  have hp:=phaseCycle_pairwise (n:=n)
  rw [hcycle] at hp
  have hnd:=phaseCycle_nodup (n:=n)
  rw [hcycle] at hnd
  have hneq : b∉pre := by
    have H:=(List.nodup_append.mp hnd).2.2
    exact fun hb=>H b hb b (by simp) rfl
  constructor
  · intro hc
    have hh:phaseLE c b:=(List.pairwise_append.mp hp).2.2 c hc b (by simp)
    rcases hh with hh|hh
    · exact hh
    · subst c; exact (hneq hc).elim
  · intro hcb
    have hc:=mem_phaseCycle c
    rw [hcycle,List.mem_append,List.mem_cons] at hc
    rcases hc with hc|hc|hc
    · exact hc
    · subst c; exact (phaseEarlier_irrefl b hcb).elim
    · have hh:phaseLE b c:=(List.pairwise_cons.mp (List.pairwise_append.mp hp).2.1).1 c hc
      rcases hh with hh|hh
      · exact (phaseEarlier_asymm hcb hh).elim
      · subst c; exact (phaseEarlier_irrefl b hcb).elim
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

lemma mem_levelQueue (q : List (Cell n)) (i : Fin n) (b : Cell n) :
    b∈levelQueue q i ↔ b∈q ∧ b.1=i := by simp [levelQueue]

lemma levelQueue_cons (b : Cell n) (q : List (Cell n)) (i : Fin n) :
    levelQueue (b::q) i=if b.1=i then b::levelQueue q i else levelQueue q i := by
  by_cases h:b.1=i <;> simp [levelQueue,h]
lemma levelQueue_rotate (b : Cell n) (q : List (Cell n)) (i : Fin n) :
    levelQueue (q++[b]) i=levelQueue q i++(if b.1=i then [b] else []) := by
  by_cases h:b.1=i <;> simp [levelQueue,h]

lemma queue_update_off {M : Type*} (w : Cell n → M) (b : Cell n) (w' : M)
    (q : List (Cell n)) (hb : b∉q) : q.map (Function.update w b w')=q.map w := by
  apply List.map_congr_left
  intro c hc
  have hcb:c≠b:=by intro h; subst c; exact hb hc
  exact Function.update_of_ne hcb _ _

end
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.ForwardChain
open ElementaryPositivity.QuantumTorus
variable {M : Type*} [AddCommGroup M]

lemma gaps_append (a c d : M) (bs : List M) :
    gaps a (bs++[c]) d=gaps a bs c++[d-c] := by
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih => simp only [List.cons_append,gaps,ih]

variable (Ω : M →+ M →+ ℤ) (p : M)

lemma positiveMutate_nonneg (r : M) (h : 0 ≤ Ω p r) : positiveMutate Ω p r=r := by
  simp only [positiveMutate,max_eq_right (by omega : -Ω p r≤0),zero_smul,add_zero]

lemma positiveMutate_minus_one (r : M) (h : Ω p r= -1) : positiveMutate Ω p r=r+p := by
  simp [positiveMutate,h]
lemma positiveMutate_minus_two (r : M) (h : Ω p r= -2) : positiveMutate Ω p r=r+p+p := by
  simp only [positiveMutate,h,neg_neg,show max (2:ℤ) 0=2 by decide]
  rw [show (2:ℤ) • p=p+p by simp [two_smul]]
  abel

lemma gaps_mutate_last (a c : M) (bs : List M)
    (ha : Ω p a=0) (hc : Ω p c= -1)
    (hb : ∀b∈bs,Ω p b=0) :
    (gaps a bs c).map (positiveMutate Ω p)=gaps a bs (c+p) := by
  induction bs generalizing a with
  | nil =>
    simp only [gaps,List.map_cons,List.map_nil,List.cons.injEq,and_true]
    rw [positiveMutate_minus_one Ω p (c-a) (by rw [map_sub,hc,ha,sub_zero])]
    abel
  | cons b bs ih =>
    have hb0:=hb b (by simp)
    have hr:Ω p (b-a)=0 := by rw [map_sub,hb0,ha,sub_self]
    simp only [gaps,List.map_cons]
    rw [positiveMutate_nonneg Ω p (b-a) (by omega),ih b hb0 (fun x hx=>hb x (by simp [hx]))]

lemma gaps_mutate_rotation (a b c : M) (bs : List M) (hp : p=b-a)
    (_ha : Ω p a=1) (hb : Ω p b=1) (hc : Ω p c= -1)
    (hs : ∀x∈bs,Ω p x=0) :
    (gaps b bs c).map (positiveMutate Ω p)=gaps a bs (c+p) := by
  cases bs with
  | nil =>
    simp only [gaps,List.map_cons,List.map_nil,List.cons.injEq,and_true]
    rw [positiveMutate_minus_two Ω p (c-b) (by rw [map_sub,hc,hb]; norm_num)]
    rw [hp]
    abel
  | cons x xs =>
    have hx:=hs x (by simp)
    simp only [gaps,List.map_cons]
    rw [positiveMutate_minus_one Ω p (x-b) (by rw [map_sub,hx,hb]; norm_num),
      gaps_mutate_last Ω p x c xs hx hc (fun z hz=>hs z (by simp [hz]))]
    congr 1
    rw [hp]
    abel

lemma gaps_rotation_perm (a b c : M) (bs : List M) (hp : p=b-a)
    (ha : Ω p a=1) (hb : Ω p b=1) (hc : Ω p c= -1)
    (hs : ∀x∈bs,Ω p x=0) :
    ((-p)::(gaps b bs c).map (positiveMutate Ω p)).Perm
      (gaps a (bs++[c+p]) c) := by
  rw [gaps_mutate_rotation Ω p a b c bs hp ha hb hc hs,gaps_append]
  have H:c-(c+p)= -p := by abel
  rw [H]
  simpa only [List.singleton_append] using (List.perm_append_comm (l₁ := [-p]) (l₂ := gaps a bs (c+p)))

lemma gaps_mutate_fixed (a c : M) (bs : List M)
    (ha : Ω p a≤0) (hc : 0≤Ω p c)
    (hb : ∀b∈bs,Ω p b=0) :
    (gaps a bs c).map (positiveMutate Ω p)=gaps a bs c := by
  induction bs generalizing a with
  | nil =>
    simp only [gaps,List.map_cons,List.map_nil]
    rw [positiveMutate_nonneg Ω p (c-a) (by rw [map_sub]; omega)]
  | cons b bs ih =>
    have hb0:=hb b (by simp)
    simp only [gaps,List.map_cons]
    rw [positiveMutate_nonneg Ω p (b-a) (by rw [map_sub,hb0]; omega),
      ih b (by omega) (fun x hx=>hb x (by simp [hx]))]
end ElementaryPositivity.ForwardChain

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RootMutationInventory
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open Classical
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)

omit [Fintype I] in
include hcoord in
lemma simpleRoot_injective : Function.Injective (simpleRoot C) := by
  intro i j h
  have H:=congrArg coord h
  change coord (C (Pi.single i 1))=coord (C (Pi.single j 1)) at H
  rw [hcoord,hcoord] at H
  by_contra hn
  have HH:=congrFun H i
  simp [hn] at HH

include hcoord in
lemma mutatedRoot_inventory (i : I) :
    simpleRoot (mutatedRoots Ω C pc) i=rootMutation Ω (simpleRoot C pc) (simpleRoot C i) := by
  by_cases hi : i=pc
  · subst i
    rw [mutatedRoot_p]
    simp [rootMutation]
  · have hn : simpleRoot C i≠simpleRoot C pc :=
      fun hh=>hi (simpleRoot_injective C coord hcoord hh)
    rw [mutatedRoot_off Ω C pc i hi]
    simp only [rootMutation,hn,ite_false, if_false,ForwardChain.positiveMutate,mutationPairing,max_comm]

include hcoord in
lemma mutatedRoot_list (is : List I) :
    is.map (simpleRoot (mutatedRoots Ω C pc))=
      (is.map (simpleRoot C)).map (rootMutation Ω (simpleRoot C pc)) := by
  rw [List.map_map]
  exact List.map_congr_left fun i _=>mutatedRoot_inventory Ω C coord hcoord pc i

lemma rootMutation_map_off (p : M) (l : List M) (hp : p∉l) :
    l.map (rootMutation Ω p)=l.map (ForwardChain.positiveMutate Ω p) := by
  apply List.map_congr_left
  intro r hr
  have hn:r≠p:=by intro h; subst r; exact hp hr
  simp [rootMutation,hn]

lemma rootMutation_rotation_perm (p a b c : M) (bs : List M) (hp : p=b-a)
    (ha : Ω p a=1) (hb : Ω p b=1) (hc : Ω p c= -1)
    (hs : ∀x∈bs,Ω p x=0) (hnd : (ForwardChain.gaps a (b::bs) c).Nodup) :
    ((ForwardChain.gaps a (b::bs) c).map (rootMutation Ω p)).Perm
      (ForwardChain.gaps a (bs++[c+p]) c) := by
  change ((b-a)::ForwardChain.gaps b bs c).Nodup at hnd
  have hnot : p∉ForwardChain.gaps b bs c := by rw [hp]; exact (List.nodup_cons.mp hnd).1
  simp only [ForwardChain.gaps,List.map_cons,←hp,rootMutation]
  rw [rootMutation_map_off Ω p _ hnot]
  exact ForwardChain.gaps_rotation_perm Ω p a b c bs hp ha hb hc hs

lemma rootMutation_gaps_fixed (p a c : M) (bs : List M)
    (ha : Ω p a≤0) (hc : 0≤Ω p c) (hb : ∀b∈bs,Ω p b=0)
    (hp : p∉ForwardChain.gaps a bs c) :
    (ForwardChain.gaps a bs c).map (rootMutation Ω p)=ForwardChain.gaps a bs c := by
  rw [rootMutation_map_off Ω p _ hp]
  exact ForwardChain.gaps_mutate_fixed Ω p a c bs ha hc hb
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
local instance monomialConjugationAddCommMonoid_r398ce1_1 : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance monomialConjugationAddGroup_r398ce1_1 : AddGroup (Torus v Ω) :=
  (Torus.instRing v Ω).toAddGroup
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
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_ForwardInventoryRotation
attribute [-simp] _root_.OAI.ElementaryPositivity.TriangularDynamics.levelNode_last _root_.OAI.ElementaryPositivity.TriangularDynamics.levelNode_zero _root_.OAI.ElementaryPositivity.TriangularDynamics.partialBridge_cycle _root_.OAI.ElementaryPositivity.TriangularDynamics.partialBridge_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus
open Classical
noncomputable section
variable {n : ℕ} {M : Type*} [AddCommGroup M]

lemma forwardInventory_level_nodup (d : Fin (n+1) → M) (w : Cell n → M) (q : List (Cell n))
    (hnd : (forwardInventory d w q).Nodup) (i : Fin n) : (levelGaps d w q i).Nodup :=
  (List.nodup_flatMap.mp hnd).1 i (List.mem_finRange i)

lemma levelGaps_root_mem (d : Fin (n+1) → M) (w : Cell n → M) (b : Cell n) (q : List (Cell n)) :
    w b-d b.1.castSucc ∈ levelGaps d w (b::q) b.1 := by
  simp [levelGaps,levelQueue_cons,ForwardChain.gaps]

lemma forwardInventory_root_mem (d : Fin (n+1) → M) (w : Cell n → M) (b : Cell n) (q : List (Cell n)) :
    w b-d b.1.castSucc ∈ forwardInventory d w (b::q) := by
  exact List.mem_flatMap.mpr ⟨b.1,List.mem_finRange _,levelGaps_root_mem d w b q⟩

private lemma pairwise_distinct {A : Type*} {R : A → A → Prop} (hs:Std.Symm R)
    {l:List A} (h:l.Pairwise R) {a b:A} (ha:a∈l) (hb:b∈l) (hab:a≠b) : R a b := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    obtain ⟨hhead,htail⟩:=List.pairwise_cons.mp h
    rcases List.mem_cons.mp ha with hax|hax
    · subst a
      rcases List.mem_cons.mp hb with hbx|hbx
      · exact (hab hbx.symm).elim
      · exact hhead b hbx
    · rcases List.mem_cons.mp hb with hbx|hbx
      · subst b; exact hs.symm _ _ (hhead a hax)
      · exact ih htail hax hbx

variable (Ω : M →+ M →+ ℤ)
lemma forwardInventory_rotation (d : Fin (n+1) → M) (w : Cell n → M) (b : Cell n) (q : List (Cell n))
    (hb : b∉q) (hnd : (forwardInventory d w (b::q)).Nodup)
    (p : M) (hp : p=w b-d b.1.castSucc)
    (hd : ∀j, Ω p (d j)=(if j=b.1.castSucc then 1 else 0)-(if j=b.1.succ then 1 else 0))
    (hw : ∀c,Ω p (w c)=if c=b then 1 else 0) :
    ((forwardInventory d w (b::q)).map (rootMutation Ω p)).Perm
      (forwardInventory d (Function.update w b (d b.1.succ+p)) (q++[b])) := by
  have hwb:Ω p (w b)=1:=by rw [hw,ite_eq_left rfl]
  have hda:Ω p (d b.1.castSucc)=1:=by rw [hd]; simp [Fin.ext_iff]
  have hdc:Ω p (d b.1.succ)= -1:=by rw [hd]; simp [Fin.ext_iff]
  have ho (i:Fin n) : ((levelQueue q i).map (Function.update w b (d b.1.succ+p)))=
      (levelQueue q i).map w := by
    apply queue_update_off
    intro hh
    exact hb (List.mem_of_mem_filter hh)
  have hlevel (i:Fin n) : ((levelGaps d w (b::q) i).map (rootMutation Ω p)).Perm
      (levelGaps d (Function.update w b (d b.1.succ+p)) (q++[b]) i) := by
    by_cases hi:b.1=i
    · subst i
      have hni:=forwardInventory_level_nodup d w (b::q) hnd b.1
      simp only [levelGaps,levelQueue_cons,ite_true, if_true,List.map_cons] at hni ⊢
      rw [levelQueue_rotate,ite_eq_left rfl,List.map_append,ho]
      simp only [List.map_cons,List.map_nil,Function.update_self]
      apply rootMutation_rotation_perm Ω p (d b.1.castSucc) (w b) (d b.1.succ) _ hp hda hwb hdc _ hni
      intro x hx
      obtain ⟨c,hc,rfl⟩:=List.mem_map.mp hx
      have hcb:c≠b:=by intro h; subst c; exact hb (List.mem_of_mem_filter hc)
      rw [hw,ite_eq_right hcb]
    · have hnot:p∉levelGaps d w (b::q) i := by
        have H:=(List.nodup_flatMap.mp hnd).2
        have hbi:b.1∈List.finRange n:=List.mem_finRange _
        have hii:i∈List.finRange n:=List.mem_finRange _
        have hpp:p∈levelGaps d w (b::q) b.1:=by rw [hp]; exact levelGaps_root_mem d w b q
        have hdis:List.Disjoint (levelGaps d w (b::q) b.1) (levelGaps d w (b::q) i):=by
          exact pairwise_distinct ⟨fun _ _ hdisjoint=>hdisjoint.symm⟩ H hbi hii hi
        exact fun hpi=>hdis hpp hpi
      have ha:Ω p (d i.castSucc)≤0:=by
        rw [hd]
        have hn:i.castSucc≠b.1.castSucc:=fun h=>hi (Fin.castSucc_inj.mp h).symm
        simp only [ite_eq_right hn]
        split_ifs <;> norm_num
      have hc:0≤Ω p (d i.succ):=by
        rw [hd]
        have hn:i.succ≠b.1.succ:=fun h=>hi (Fin.succ_inj.mp h).symm
        simp only [ite_eq_right hn,sub_zero]
        split_ifs <;> norm_num
      simp only [levelGaps,levelQueue_cons,ite_eq_right hi] at hnot ⊢
      rw [levelQueue_rotate,ite_eq_right hi,List.append_nil,ho]
      apply List.Perm.of_eq
      apply rootMutation_gaps_fixed Ω p _ _ _ ha hc _ hnot
      intro x hx
      obtain ⟨c,hc,rfl⟩:=List.mem_map.mp hx
      have hcb:c≠b:=by intro h; subst c; exact hb (List.mem_of_mem_filter hc)
      rw [hw,ite_eq_right hcb]
  rw [forwardInventory,List.map_flatMap]
  exact (List.Perm.refl _).flatMap (fun i _=>hlevel i)
end
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.QuantumTorus
open Classical
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]

variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M) (pc:I) (e:M →+ E)

lemma rootDegreeCovector_exists (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i))) :
    ∃L:Module.Dual ℝ E,∀n m,HasRootDegree C n m → L (e m)=(n:ℝ) := by
  obtain ⟨D,hD⟩:=realRootCoordinates_exists C e hC
  let L:Module.Dual ℝ E:=∑i,(LinearMap.proj i).comp D
  refine ⟨L,fun n m hm=>covector_root_eval C e L ?_ hm⟩
  intro i
  simp only [L,LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.proj_apply,
    real_coordinate_simple C e D hD]
  simp
end
end ElementaryPositivity.QuantumTorus

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
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus
open Classical
noncomputable section
variable {n:ℕ} {M E I:Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]

variable (Ω:M →+ M →+ ℤ) {e:M →+ E}
lemma freeChart_inventory_step (ch:FreeChart (I:=I) e) (is:List I)
    (his:is.Nodup) (_hall:∀i,i∈is)
    (d:Fin (n+1) → M) (w:Cell n → M) (b:Cell n) (q:List (Cell n))
    (hb:b∉q) (hinv:(is.map (simpleRoot ch.roots)).Perm (forwardInventory d w (b::q)))
    (p:M) (hp:p=w b-d b.1.castSucc)
    (hd:∀j,Ω p (d j)=(if j=b.1.castSucc then 1 else 0)-(if j=b.1.succ then 1 else 0))
    (hw:∀c,Ω p (w c)=if c=b then 1 else 0) :
    ∃pc:I,simpleRoot ch.roots pc=p ∧
      (is.map (simpleRoot (ch.mutate Ω pc).roots)).Perm
        (forwardInventory d (Function.update w b (d b.1.succ+p)) (q++[b])) := by
  have hmem:p∈forwardInventory d w (b::q):=by rw [hp]; exact forwardInventory_root_mem d w b q
  have hm:p∈is.map (simpleRoot ch.roots):=hinv.mem_iff.mpr hmem
  obtain ⟨pc,_,hpc⟩:=List.mem_map.mp hm
  refine ⟨pc,hpc,?_⟩
  have hnd:(forwardInventory d w (b::q)).Nodup:=
    hinv.nodup_iff.mp (his.map (simpleRoot_injective ch.roots ch.coord ch.retract))
  change (is.map (simpleRoot (mutatedRoots Ω ch.roots pc))).Perm _
  rw [mutatedRoot_list Ω ch.roots ch.coord ch.retract pc,hpc]
  exact (hinv.map (rootMutation Ω p)).trans (forwardInventory_rotation Ω d w b q hb hnd p hp hd hw)
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_ForwardPolynomialMutation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits
open Classical
noncomputable section
variable {n:ℕ} {M E I:Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (e:M →+ E) (he:Function.Injective e)
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)
variable (hcomp:∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (hnd:∀r≠0,∃m,Ω r m≠0)

omit [AddCommGroup M] in
lemma vertexDisplay_update (d:Fin (n+1) → M) (w:Cell n → M) (b:Cell n) (w':M) :
    vertexDisplay d (Function.update w b w')=Function.update (vertexDisplay d w) (.inr b) w' := by
  funext a
  cases a with
  | inl a => simp [vertexDisplay]
  | inr a => by_cases h:a=b <;> simp [vertexDisplay,h]

include hΩ he hS hcomp hnd in
lemma freeChart_polynomial_step (ch:FreeChart (I:=I) e) (is:List I)
    (his:is.Nodup) (hall:∀i,i∈is)
    (d:Fin (n+1) → M) (w:Cell n → M) (b:Cell n) (q:List (Cell n))
    (hb:b∉q) (hinv:(is.map (simpleRoot ch.roots)).Perm (forwardInventory d w (b::q)))
    (p:M) (hp:p=w b-d b.1.castSucc)
    (hd:∀j,Ω p (d j)=(if j=b.1.castSucc then 1 else 0)-(if j=b.1.succ then 1 else 0))
    (hw:∀c,Ω p (w c)=if c=b then 1 else 0)
    (hdd:Ω (d b.1.castSucc) (d b.1.succ)=0) {N:ℕ} (f:ElementaryExpr N) :
    ∃pc:I,simpleRoot ch.roots pc=p ∧
      (is.map (simpleRoot (ch.mutate Ω pc).roots)).Perm
        (forwardInventory d (Function.update w b (d b.1.succ+p)) (q++[b])) ∧
      ∀r,polynomialSectionIncoming Ω ch.roots ch.coord
          (f.eval LaurentRay.vUnit Ω (vertexDisplay d w)) r=
        polynomialSectionIncoming Ω (ch.mutate Ω pc).roots (ch.mutate Ω pc).coord
          (f.eval LaurentRay.vUnit Ω (vertexDisplay d (Function.update w b (d b.1.succ+p))))
          (mutationIncomingLabel Ω p r) := by
  obtain ⟨pc,hpc,hpi⟩:=freeChart_inventory_step Ω ch is his hall d w b q hb hinv p hp hd hw
  cases hpc
  refine ⟨pc,rfl,hpi,?_⟩
  have hF:PureInitialRelation Ω hΩ ch.roots ch.coord ch.retract pc
      (f.eval LaurentRay.vUnit Ω (vertexDisplay d w))
      (f.eval LaurentRay.vUnit Ω (vertexDisplay d (Function.update w b (d b.1.succ+simpleRoot ch.roots pc)))) := by
    unfold PureInitialRelation
    rw [vertexDisplay_update]
    symm
    apply ElementaryExpr.rotation LaurentRay.vUnit Ω hΩ _ (simpleRoot ch.roots pc) _ (vertexDisplay d w)
      (.inl b.1.castSucc) (.inr b) (.inl b.1.succ) (by simp) (by simp)
      (by simp [Fin.ext_iff]) _ _ _ hdd _ f
    · change w b=d b.1.castSucc+simpleRoot ch.roots pc
      rw [hp]; abel
    · change Ω (simpleRoot ch.roots pc) (d b.1.castSucc)=1
      rw [hd]; simp [Fin.ext_iff]
    · change Ω (simpleRoot ch.roots pc) (d b.1.succ)= -1
      rw [hd]; simp [Fin.ext_iff]
    · intro x hxa hxb hxc
      cases x with
      | inl a =>
        change Ω (simpleRoot ch.roots pc) (d a)=0
        rw [hd]
        have ha:a≠b.1.castSucc:=by simpa using hxa
        have hc:a≠b.1.succ:=by simpa using hxc
        simp [ha,hc]
      | inr c =>
        change Ω (simpleRoot ch.roots pc) (w c)=0
        rw [hw,ite_eq_right (by simpa using hxb)]
  obtain ⟨L,hL⟩:=rootDegreeCovector_exists ch.roots e ch.independent
  intro r
  have H:=polynomialSectionIncoming_mutation Ω hΩ ch.roots ch.coord ch.retract pc e he S hS hcomp
    L hL hnd ch.independent _ _ hF r
  simpa only [FreeChart.mutate] using H
end
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.TriangularDynamics
open Classical
noncomputable section
variable {n:ℕ}

lemma partialBridge_scheduled (L:ℕ) {pre post:List (Cell n)} {b:Cell n}
    (hc:phaseCycle n=pre++b::post) : partialBridge L pre=scheduledBridge L b := by
  funext c
  simp only [partialBridge,scheduledBridge,prefix_before hc]
lemma eventRoot_partial (L:ℕ) {pre post:List (Cell n)} {b:Cell n}
    (hc:phaseCycle n=pre++b::post) : eventRoot cellLevel L b=partialBridge L pre b-anchor b.1.castSucc := by
  rw [partialBridge_scheduled L hc,scheduledBridge_self]
  simp only [eventRoot,cellLevel]
  abel
lemma cycle_head_not_mem {pre post:List (Cell n)} {b:Cell n}
    (hc:phaseCycle n=pre++b::post) : b∉post++pre := by
  have hn:=phaseCycle_nodup (n:=n)
  rw [hc] at hn
  obtain ⟨hpre,hrest,hdis⟩:=List.nodup_append.mp hn
  have hpost: b∉post:=(List.nodup_cons.mp hrest).1
  have hp:b∉pre:=fun hb=>hdis b hb b (by simp) rfl
  simpa using And.intro hpost hp

lemma partialBridge_step (L:ℕ) (pre:List (Cell n)) (b:Cell n) (_hb:b∉pre) :
    partialBridge L (pre++[b])=
      Function.update (partialBridge L pre) b (anchor b.1.succ+eventRoot cellLevel L b) := by
  funext c
  by_cases hc:c=b
  · subst c
    simp only [partialBridge,List.mem_append,List.mem_singleton,or_true,ite_true, if_true,Function.update_self,
      eventRoot,delta,cellLevel,add_zsmul,one_zsmul]
    abel
  · simp only [partialBridge,List.mem_append,List.mem_singleton,hc,or_false,
      Function.update_of_ne hc]

lemma periodFunctional_anchor (i:Fin n) (L:ℕ) (a:Fin (n+1)) :
    periodFunctional cellLevel i L (anchor a)=if a.val≤ i.val then 1 else 0 := by
  change cutPrefix cellLevel i (anchor a)+(L:ℤ) • levelTotal cellLevel i (anchor a)=_
  rw [levelTotal_anchor,smul_zero,add_zero]
  exact cutPrefix_single cellLevel i (.inl a) 1
lemma periodFunctional_bridge (i:Fin n) (L:ℕ) (b:Cell n) :
    periodFunctional cellLevel i L (periodBridge L b)=if b.1.val≤ i.val then 1 else 0 := by
  have hb:eventRoot cellLevel L b=periodBridge L b-anchor b.1.castSucc:=by
    unfold eventRoot periodBridge cellLevel; abel
  have H:=periodFunctional_eventRoot cellLevel i L b
  rw [hb,map_sub,periodFunctional_anchor] at H
  simpa only [Fin.val_castSucc] using sub_eq_zero.mp H

lemma gaps_cut_nonpos {M:Type*} [AddCommGroup M] (ell:M →+ ℤ) (a c:M) (bs:List M) (K:ℤ)
    (ha:K≤ell a) (hc:ell c≤K) (hb:∀b∈bs,ell b=K) :
    ∀r∈ForwardChain.gaps a bs c,ell r≤0 := by
  induction bs generalizing a with
  | nil =>
    intro r hr
    have hr:r=c-a:=by simpa [ForwardChain.gaps] using hr
    rw [hr,map_sub]
    omega
  | cons b bs ih =>
    have hbb:=hb b (by simp)
    intro r hr
    rcases List.mem_cons.mp hr with hr|hr
    · rw [hr,map_sub,hbb]; omega
    · apply ih b (by omega) (fun x hx=>hb x (by simp [hx])) r hr

lemma periodInventory_cut_nonpos (i:Fin n) (L:ℕ) (q:List (Cell n)) :
    ∀r∈forwardInventory anchor (periodBridge L) q,periodFunctional cellLevel i L r≤0 := by
  intro r hr
  obtain ⟨j,_,hr⟩:=List.mem_flatMap.mp hr
  apply gaps_cut_nonpos (periodFunctional cellLevel i L) (anchor j.castSucc) (anchor j.succ)
    ((levelQueue q j).map (periodBridge L)) (if j.val≤ i.val then 1 else 0) _ _ _ r hr
  · rw [periodFunctional_anchor]; rfl
  · rw [periodFunctional_anchor]
    simp only [Fin.val_succ]
    split_ifs <;> omega
  · intro x hx
    obtain ⟨b,hb,rfl⟩:=List.mem_map.mp hx
    have hbj: b.1=j:=(mem_levelQueue q j b).mp hb |>.2
    rw [periodFunctional_bridge,hbj]

end
end ElementaryPositivity.TriangularDynamics

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

local instance polynomialSectionRing_r398ce1_1 : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance polynomialSectionAddCommMonoid_r398ce1_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance polynomialSectionAddGroup_r398ce1_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
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

lemma rootDegree_cut_bound (ell:M →+ ℤ) (hc:∀i,ell (simpleRoot C i)≤0)
    {d:ℕ} {m:M} (hm:HasRootDegree C d m) : ell m≤0 := by
  obtain ⟨a,_,rfl⟩:=hm
  have hex:(fun i=>(a i:ℤ))=∑i,Pi.single i (a i:ℤ):=by
    ext i
    simp
  rw [hex,map_sum,map_sum]
  apply Finset.sum_nonpos
  intro i _
  have H:C (Pi.single i (a i:ℤ))=(a i:ℤ) • simpleRoot C i:=by
    rw [simpleRoot,←map_zsmul]
    congr 1
    ext j
    simp only [Pi.smul_apply,Pi.single_apply,smul_eq_mul]
    split_ifs <;> simp
  rw [H,map_zsmul,smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) (hc i)

include hΩ in
lemma polynomialSection_cut_bound (h:M →+ ℝ) (F:Torus LaurentRay.vUnit Ω)
    (ell:M →+ ℤ) (K:ℤ) (hc:∀i,ell (simpleRoot C i)≤0)
    (hF:∀b∈F.support,ell b≤K) (m:M)
    (hm:polynomialSectionCoefficient Ω C coord h F m≠0) : ell m≤K := by
  obtain ⟨b,hb,d,hd⟩:=polynomialSection_support Ω hΩ C coord h F m hm
  have HH:=rootDegree_cut_bound C ell hc hd
  rw [map_sub] at HH
  have := hF b hb
  omega

include hΩ in
lemma polynomialIncoming_cut_bound (F:Torus LaurentRay.vUnit Ω)
    (ell:M →+ ℤ) (K:ℤ) (hc:∀i,ell (simpleRoot C i)≤0)
    (hF:∀b∈F.support,ell b≤K) (m:M)
    (hm:polynomialSectionIncoming Ω C coord F m≠0) : ell m≤K :=
  polynomialSection_cut_bound Ω hΩ C coord (incomingCovector Ω m) F ell K hc hF m hm
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

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularPeriodTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits
open Classical
noncomputable section
variable {n:ℕ} {M E I:Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (e:M →+ E) (he:Function.Injective e)
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)
variable (hcomp:∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (hnd:∀r≠0,∃m,Ω r m≠0)
variable (h:Lattice n (Cell n) →+ M) (hform:∀x y,Ω (h x) (h y)=triangularOmega n x y)

include hform in
lemma mutationIncomingLabel_map (p m:Lattice n (Cell n)) :
    mutationIncomingLabel Ω (h p) (h m)=h (mutationIncomingLabel (triangularOmega n) p m) := by
  simp only [mutationIncomingLabel,hform,map_add,map_zsmul]

include hΩ he hS hcomp hnd hform in
lemma partial_period_transport (is:List I) (his:is.Nodup) (hall:∀i,i∈is)
    (L:ℕ) (rest:List (Cell n)) (pre:List (Cell n))
    (hcycle:phaseCycle n=pre++rest) (ch:FreeChart (I:=I) e)
    (hinv:(is.map (simpleRoot ch.roots)).Perm
      (forwardInventory (h ∘ anchor) (h ∘ partialBridge L pre) (rest++pre)))
    {N:ℕ} (f:ElementaryExpr N) :
    ∃ch':FreeChart (I:=I) e,
      (is.map (simpleRoot ch'.roots)).Perm
        (forwardInventory (h ∘ anchor) (h ∘ periodBridge (L+1)) (phaseCycle n)) ∧
      ∀m,polynomialSectionIncoming Ω ch.roots ch.coord
          (f.eval LaurentRay.vUnit Ω (vertexDisplay (h ∘ anchor) (h ∘ partialBridge L pre))) (h m)=
        polynomialSectionIncoming Ω ch'.roots ch'.coord
          (f.eval LaurentRay.vUnit Ω (vertexDisplay (h ∘ anchor) (h ∘ periodBridge (L+1))))
          (h (rest.foldl (rotate (triangularOmega n) cellLevel L) m)) := by
  induction rest generalizing pre ch with
  | nil =>
    have hpre:pre=phaseCycle n:=by simpa using hcycle.symm
    subst pre
    refine ⟨ch,?_,?_⟩
    · simpa only [List.nil_append,partialBridge_cycle] using hinv
    · intro m
      simp only [partialBridge_cycle,List.foldl_nil]
  | cons b post ih =>
    have hb:=cycle_head_not_mem hcycle
    have hbp:b∉pre:=fun hh=>hb (List.mem_append.mpr (Or.inr hh))
    have hp:h (eventRoot cellLevel L b)= (h ∘ partialBridge L pre) b - (h ∘ anchor) b.1.castSucc:=by
      rw [eventRoot_partial L hcycle,map_sub]
      rfl
    have hd:∀j,Ω (h (eventRoot cellLevel L b)) ((h ∘ anchor) j)=
        (if j=b.1.castSucc then 1 else 0)-(if j=b.1.succ then 1 else 0):=by
      intro j
      exact (hform _ _).trans (scheduledRoot_anchor L b j)
    have hw:∀c,Ω (h (eventRoot cellLevel L b)) ((h ∘ partialBridge L pre) c)=if c=b then 1 else 0:=by
      intro c
      change Ω (h (eventRoot cellLevel L b)) (h (partialBridge L pre c))=_
      rw [hform,partialBridge_scheduled L hcycle]
      exact scheduledRoot_bridge L b c
    have hdd:Ω ((h ∘ anchor) b.1.castSucc) ((h ∘ anchor) b.1.succ)=0:=by
      simp only [Function.comp_apply,hform,omega_anchors]
    have hiv:(is.map (simpleRoot ch.roots)).Perm
        (forwardInventory (h ∘ anchor) (h ∘ partialBridge L pre) (b::(post++pre))):=by
      simpa only [List.cons_append] using hinv
    obtain ⟨pc,hpc,hpi,hF⟩:=freeChart_polynomial_step Ω hΩ e he S hS hcomp hnd ch is his hall
      (h ∘ anchor) (h ∘ partialBridge L pre) b (post++pre) hb hiv
      (h (eventRoot cellLevel L b)) hp hd hw hdd f
    have hnew:Function.update (h ∘ partialBridge L pre) b
        ((h ∘ anchor) b.1.succ+h (eventRoot cellLevel L b))=h ∘ partialBridge L (pre++[b]):=by
      rw [partialBridge_step L pre b hbp,Function.comp_update,map_add]
      rfl
    rw [hnew] at hpi hF
    have hc':phaseCycle n=(pre++[b])++post:=by rw [hcycle]; simp only [List.append_assoc,List.singleton_append]
    have hi':(is.map (simpleRoot (ch.mutate Ω pc).roots)).Perm
        (forwardInventory (h ∘ anchor) (h ∘ partialBridge L (pre++[b])) (post++(pre++[b]))):=by
      simpa only [List.append_assoc] using hpi
    obtain ⟨ch',hfin,heq⟩:=ih (pre++[b]) hc' (ch.mutate Ω pc) hi'
    refine ⟨ch',hfin,?_⟩
    intro m
    rw [hF,mutationIncomingLabel_map Ω h hform]
    exact heq (rotate (triangularOmega n) cellLevel L m b)

include hΩ he hS hcomp hnd hform in
lemma full_period_transport (is:List I) (his:is.Nodup) (hall:∀i,i∈is)
    (L:ℕ) (ch:FreeChart (I:=I) e)
    (hinv:(is.map (simpleRoot ch.roots)).Perm
      (forwardInventory (h ∘ anchor) (h ∘ periodBridge L) (phaseCycle n)))
    {N:ℕ} (f:ElementaryExpr N) :
    ∃ch':FreeChart (I:=I) e,
      (is.map (simpleRoot ch'.roots)).Perm
        (forwardInventory (h ∘ anchor) (h ∘ periodBridge (L+1)) (phaseCycle n)) ∧
      ∀m,polynomialSectionIncoming Ω ch.roots ch.coord
          (f.eval LaurentRay.vUnit Ω (vertexDisplay (h ∘ anchor) (h ∘ periodBridge L))) (h m)=
        polynomialSectionIncoming Ω ch'.roots ch'.coord
          (f.eval LaurentRay.vUnit Ω (vertexDisplay (h ∘ anchor) (h ∘ periodBridge (L+1))))
          (h (period (triangularOmega n) cellLevel (phaseCycle n) L m)) := by
  have hi:(is.map (simpleRoot ch.roots)).Perm
      (forwardInventory (h ∘ anchor) (h ∘ partialBridge L []) (phaseCycle n++[])):=by
    simpa only [partialBridge_nil,List.append_nil] using hinv
  simpa only [partialBridge_nil,period] using partial_period_transport Ω hΩ e he S hS hcomp hnd h hform
    is his hall L (phaseCycle n) [] rfl ch hi f
end
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits
open Classical
noncomputable section
variable {n:ℕ} {M E I:Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (e:M →+ E) (he:Function.Injective e)
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)
variable (hcomp:∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (hnd:∀r≠0,∃m,Ω r m≠0)
variable (h:Lattice n (Cell n) →+ M) (hform:∀x y,Ω (h x) (h y)=triangularOmega n x y)
variable (retract:M →+ Lattice n (Cell n)) (hret:∀m,retract (h m)=m)

omit [FiniteDimensional ℝ E] in
include hΩ hret in
lemma periodIncoming_cut [FiniteDimensional ℝ E] (is:List I) (hall:∀i,i∈is)
    (L:ℕ) (ch:FreeChart (I:=I) e)
    (hinv:(is.map (simpleRoot ch.roots)).Perm
      (forwardInventory (h ∘ anchor) (h ∘ periodBridge L) (phaseCycle n)))
    {N:ℕ} (f:ElementaryExpr N) (m:Lattice n (Cell n))
    (hm:polynomialSectionIncoming Ω ch.roots ch.coord
      (f.eval LaurentRay.vUnit Ω (vertexDisplay (h ∘ anchor) (h ∘ periodBridge L))) (h m)≠0) (i:Fin n) :
    periodFunctional cellLevel i L m≤(N:ℤ) := by
  let ell:M →+ ℤ:=(periodFunctional cellLevel i L).comp retract
  have hell (x:Lattice n (Cell n)):ell (h x)=periodFunctional cellLevel i L x:=by
    change periodFunctional cellLevel i L (retract (h x))=_
    rw [hret]
  have hc:∀j,ell (simpleRoot ch.roots j)≤0:=by
    intro j
    have H:=hinv.mem_iff.mp (List.mem_map.mpr ⟨j,hall j,rfl⟩)
    rw [forwardInventory_map] at H
    obtain ⟨r,hr,heq⟩:=List.mem_map.mp H
    rw [←heq,hell]
    exact periodInventory_cut_nonpos i L (phaseCycle n) r hr
  have hv:∀x,ell (vertexDisplay (h ∘ anchor) (h ∘ periodBridge L) x)≤1:=by
    intro x
    cases x with
    | inl a =>
      change ell (h (anchor a))≤1
      rw [hell,periodFunctional_anchor]
      split_ifs <;> omega
    | inr b =>
      change ell (h (periodBridge L b))≤1
      rw [hell,periodFunctional_bridge]
      split_ifs <;> omega
  have hf:=f.cutSupported LaurentRay.vUnit Ω ell (vertexDisplay (h ∘ anchor) (h ∘ periodBridge L)) hv
  have H:=polynomialIncoming_cut_bound Ω hΩ ch.roots ch.coord _ ell N hc hf (h m) hm
  rwa [hell] at H

include hΩ he hS hcomp hnd hform in
lemma complete_history_transport (is:List I) (his:is.Nodup) (hall:∀i,i∈is)
    (ch:FreeChart (I:=I) e)
    (hinv:(is.map (simpleRoot ch.roots)).Perm
      (forwardInventory (h ∘ anchor) (h ∘ periodBridge 0) (phaseCycle n)))
    {N:ℕ} (f:ElementaryExpr N) (m:Lattice n (Cell n)) (L:ℕ) :
    ∃ch':FreeChart (I:=I) e,
      (is.map (simpleRoot ch'.roots)).Perm
        (forwardInventory (h ∘ anchor) (h ∘ periodBridge L) (phaseCycle n)) ∧
      polynomialSectionIncoming Ω ch.roots ch.coord
          (f.eval LaurentRay.vUnit Ω (vertexDisplay (h ∘ anchor) (h ∘ periodBridge 0))) (h m)=
        polynomialSectionIncoming Ω ch'.roots ch'.coord
          (f.eval LaurentRay.vUnit Ω (vertexDisplay (h ∘ anchor) (h ∘ periodBridge L)))
          (h (history (triangularOmega n) cellLevel (phaseCycle n) m L)) := by
  induction L with
  | zero => exact ⟨ch,hinv,rfl⟩
  | succ L ih =>
    obtain ⟨ch',hi,heq⟩:=ih
    obtain ⟨ch'',hi',heq'⟩:=full_period_transport Ω hΩ e he S hS hcomp hnd h hform is his hall L ch' hi f
    exact ⟨ch'',hi',heq.trans (heq' _)⟩

include hΩ he hS hcomp hnd hform hret in
lemma genuine_history_cut_deficit_oai (is:List I) (his:is.Nodup) (hall:∀i,i∈is)
    (ch:FreeChart (I:=I) e)
    (hinv:(is.map (simpleRoot ch.roots)).Perm
      (forwardInventory (h ∘ anchor) (h ∘ periodBridge 0) (phaseCycle n)))
    {N:ℕ} (f:ElementaryExpr N) (m:Lattice n (Cell n))
    (hm:polynomialSectionIncoming Ω ch.roots ch.coord
      (f.eval LaurentRay.vUnit Ω (vertexDisplay (h ∘ anchor) (h ∘ periodBridge 0))) (h m)≠0)
    (L:ℕ) (i:Fin n) :
    0 ≤ cutDeficit cellLevel i N L (history (triangularOmega n) cellLevel (phaseCycle n) m L) := by
  obtain ⟨ch',hi,heq⟩:=complete_history_transport Ω hΩ e he S hS hcomp hnd h hform is his hall ch hinv f m L
  have hm':polynomialSectionIncoming Ω ch'.roots ch'.coord
      (f.eval LaurentRay.vUnit Ω (vertexDisplay (h ∘ anchor) (h ∘ periodBridge L)))
      (h (history (triangularOmega n) cellLevel (phaseCycle n) m L))≠0:=by rwa [←heq]
  have H:=periodIncoming_cut Ω hΩ e h retract hret is hall L ch' hi f _ hm' i
  unfold cutDeficit
  omega
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.ElementaryPositivity.TriangularDynamics.genuine_history_cut_deficit_oai.{u_1, u_2, u_3} := @OAI.ElementaryPositivity.TriangularDynamics.genuine_history_cut_deficit_oai.{u_1, u_2, u_3}
