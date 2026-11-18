-- Prove2me | solution 1 for OAI.ElementaryPositivity.TriangularDynamics.graph_common_history
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T19:02:02.874821+00:00
-- url     : https://prove2.me/submissions/dfa8fb26-43e6-45a6-9a89-091559ff1bc6

import Mathlib
import Definitions.Def_ElementaryPositivity
import Definitions.Def_OAIQ368Chrom058
import Theorems.Thm_OAI_ElementaryPositivity_QuantumTorus_polynomial_common_history
import Theorems.Thm_OAI_ElementaryPositivity_TriangularDynamics_monomial_producer_supported
import Theorems.Thm_OAI_ElementaryPositivity_TriangularDynamics_triangularIncoming_anchorCoeff
import Theorems.Thm_OAI_ElementaryPositivity_TriangularDynamics_triangularPure_equal

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

local instance instAddGroupTorusLaurentSeriesRat_r90e676_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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

local instance instAddGroupTorusLaurentSeriesRat_3_r90e676_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instSubTorusLaurentSeriesRat_3_r90e676_1 : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
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
local instance homogeneousElementaryExpressionsAddCommMonoid_r90e676_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
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

local instance elementaryExpressionBoundsRing_r90e676_1 : Ring (Torus v Ω) := Torus.instRing v Ω
local instance elementaryExpressionBoundsAddCommMonoid_r90e676_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance elementaryExpressionBoundsAddGroup_r90e676_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_OrderedIndependentProduct
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instAddCommGroup _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
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
variable (v:Kˣ) (Ω:M →+ M →+ ℤ)
variable (u:V → M)

lemma wordEnergy_eq_pairs {r:ℕ} (a:Fin r → M) :
    wordEnergy Ω a=∑i:Fin r,∑j:Fin r,if i < j then Ω (a i) (a j) else 0 := by
  induction r with
  | zero=>simp [wordEnergy]
  | succ r ih=>
    rw [wordEnergy,ih,Fin.sum_univ_succ]
    simp only [Fin.sum_univ_succ,Fin.not_lt_zero,ite_false, if_false,zero_add,Fin.succ_lt_succ_iff,
      Fin.succ_pos,ite_true, if_true]
    rw [wordExponent,map_sum]

local instance orderedIndependentProductRing_r90e676_1 : Ring (Torus v Ω) := Torus.instRing v Ω
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.orderedIndependentProductAddCommMonoid
local instance orderedIndependentProductAddGroup_r90e676_1 : AddGroup (Torus v Ω) :=
  (Torus.instRing v Ω).toAddGroup
local instance orderedIndependentProductNonUnitalSemiring_r90e676_1 : NonUnitalSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalSemiring
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.orderedIndependentProductNonUnitalNonAssocSemiring
local instance orderedIndependentProductAddCommGroup_r90e676_1 : AddCommGroup (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommGroup
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.orderedIndependentProductAddMonoid
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.orderedIndependentProductSemiring
local instance orderedIndependentProductNonAssocSemiring_r90e676_1 : NonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonAssocSemiring
local instance orderedIndependentProductDistrib_r90e676_1 : Distrib (Torus v Ω) :=
  (Torus.instRing v Ω).toDistrib
local instance orderedIndependentProductMonoid_r90e676_1 : Monoid (Torus v Ω) :=
  (Torus.instRing v Ω).toMonoid
lemma ordered_monomial_product {r:ℕ} (a:Fin r → M) :
    (List.ofFn (fun i=>Torus.X v Ω (a i))).prod=
      Torus.monomial v Ω (wordExponent a) (↑(v^(wordEnergy Ω a))) := by
  induction r with
  | zero=>simp [wordEnergy,wordExponent,Torus.X,Torus.monomial]; rfl
  | succ r ih=>
    rw [List.ofFn_succ,List.prod_cons,ih]
    change Torus.monomial v Ω (a 0) 1 * _=_
    rw [Torus.monomial_mul_monomial,wordEnergy]
    simp only [wordExponent,Fin.sum_univ_succ,zpow_add,Units.val_mul]
    congr 1
    rw [one_mul,mul_comm]

omit [Fintype V] in
lemma independentTerm_product {r:ℕ} (a:Fin r → ℕ) (s:Fin r → Finset V) :
    (List.ofFn (fun i=>independentTerm v Ω u (a i) (s i))).prod=
      if BlockValid Ω u a s then
        Torus.monomial v Ω (wordExponent (blockLabels u s)) (↑(v^(wordEnergy Ω (blockLabels u s)))) else 0 := by
  by_cases h:BlockValid Ω u a s
  · rw [ite_eq_left h]
    have H:(fun i=>independentTerm v Ω u (a i) (s i))=(fun i=>Torus.X v Ω (blockLabels u s i)):=by
      funext i
      exact ite_eq_left (h i)
    rw [H,ordered_monomial_product]
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩:=not_forall.mp h
    apply List.prod_eq_zero
    apply List.mem_ofFn.mpr
    exact ⟨i,by simp only [independentTerm,ite_eq_right hi]⟩

lemma independentElement_product {r:ℕ} (a:Fin r → ℕ) :
    (List.ofFn (fun i=>independentElement v Ω u (a i))).prod=
      ∑s:Fin r → Finset V,
        if BlockValid Ω u a s then
          Torus.monomial v Ω (wordExponent (blockLabels u s)) (↑(v^(wordEnergy Ω (blockLabels u s)))) else 0 := by
  have H:∀r:ℕ,∀a:Fin r → ℕ,
      (List.ofFn (fun i=>independentElement v Ω u (a i))).prod=
        ∑s:Fin r → Finset V,(List.ofFn (fun i=>independentTerm v Ω u (a i) (s i))).prod := by
    intro r
    induction r with
    | zero=>intro a; simp
    | succ r ih=>
      intro a
      rw [List.ofFn_succ,List.prod_cons,ih,independentElement]
      erw [Finset.sum_mul]
      simp only [Finset.mul_sum]
      rw [←Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (r+1)=>Finset V)),Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro s hs
      rw [List.ofFn_succ,List.prod_cons]
      rfl
  rw [H]
  apply Finset.sum_congr rfl
  intro s hs
  exact independentTerm_product v Ω u a s
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_SquarefreeCoefficient
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity
open scoped BigOperators
open Classical
noncomputable section
lemma sum_eq_subtype {A R:Type*} [Fintype A] [AddCommMonoid R]
    (p:A → Prop) [DecidablePred p] (f:A → R) (hf:∀a,¬p a → f a=0) :
    ∑a,f a=∑a:{a // p a},f a.val := by
  rw [←Fintype.sum_subtype_add_sum_subtype p f]
  have H:(∑a:{a // ¬p a},f a.val)=0:=Finset.sum_eq_zero (fun a _=>hf a.val a.property)
  rw [H,add_zero]

namespace QuantumTorus
variable {K M V:Type*} [Field K] [AddCommGroup M] [Fintype V] [DecidableEq V]
variable (v:Kˣ) (Ω:M →+ M →+ ℤ)
variable (c:(V → ℤ) →+ M) (hc:Function.Injective c)
variable {n r:ℕ} (b:Fin n ↪ V)

omit [Fintype V] in
lemma blockLabels_sum (s:Fin r → Finset V) :
    wordExponent (blockLabels (fun x=>c (Pi.single x 1)) s)=c (SquarefreeBlocks.vector s) := by
  simp only [wordExponent,blockLabels,SquarefreeBlocks.vector,map_sum]

local instance squarefreeCoefficientRing_r90e676_1 : Ring (Torus v Ω) := Torus.instRing v Ω
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.squarefreeCoefficientAddCommMonoid
local instance squarefreeCoefficientAddGroup_r90e676_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
include hc in
lemma independent_product_squarefree (a:Fin r → ℕ) :
    ((List.ofFn (fun i=>independentElement v Ω (fun x=>c (Pi.single x 1)) (a i))).prod)
        (c (SquarefreeBlocks.target b))=
      ∑κ:Fin n → Fin r,
        if BlockValid Ω (fun x=>c (Pi.single x 1)) a (SquarefreeBlocks.blocks b κ) then
          ↑(v^(wordEnergy Ω (blockLabels (fun x=>c (Pi.single x 1)) (SquarefreeBlocks.blocks b κ)))) else 0 := by
  rw [independentElement_product]
  have hs:∀(s:Finset (Fin r → Finset V)) (f:(Fin r → Finset V) → Torus v Ω),
      (∑a∈s,f a) (c (SquarefreeBlocks.target b))=∑a∈s,f a (c (SquarefreeBlocks.target b)):=by
    intro s f
    induction s using Finset.induction with
    | empty=>rfl
    | @insert a s ha ih=>
      rw [Finset.sum_insert ha,Finset.sum_insert ha]
      change f a _+(∑i∈s,f i) _=_
      rw [ih]
  rw [hs]
  let term (s:Fin r → Finset V):K:=
    (if BlockValid Ω (fun x=>c (Pi.single x 1)) a s then
      Torus.monomial v Ω (wordExponent (blockLabels (fun x=>c (Pi.single x 1)) s))
        (↑(v^(wordEnergy Ω (blockLabels (fun x=>c (Pi.single x 1)) s)))) else 0)
        (c (SquarefreeBlocks.target b))
  change (∑s,term s)=_
  rw [sum_eq_subtype (fun s=>SquarefreeBlocks.vector s=SquarefreeBlocks.target b) term]
  · rw [←Equiv.sum_comp (SquarefreeBlocks.equiv b).symm]
    apply Finset.sum_congr rfl
    intro κ hκ
    change term (SquarefreeBlocks.blocks b κ)=_
    unfold term
    split_ifs with h
    · rw [blockLabels_sum,Torus.monomial,SquarefreeBlocks.blocks_vector]
      exact Finsupp.single_eq_same
    · rfl
  · intro s hs
    unfold term
    split_ifs
    · rw [blockLabels_sum,Torus.monomial]
      exact Finsupp.single_eq_of_ne (fun h=>hs (hc h.symm))
    · rfl
end QuantumTorus
end
end ElementaryPositivity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Histories_ColorBlockEnergy
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instAddCommGroup _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
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
variable {M V:Type*} [AddCommGroup M] [Fintype V] [DecidableEq V]
variable (Ω:M →+ M →+ ℤ) (u:V → M)
variable {n r:ℕ} (b:Fin n ↪ V) (κ:Fin n → Fin r)

omit [Fintype V] [DecidableEq V] in
lemma wordEnergy_blocks :
    wordEnergy Ω (blockLabels u (SquarefreeBlocks.blocks b κ))=
      ∑i:Fin n,∑j:Fin n,if κ i<κ j then Ω (u (b i)) (u (b j)) else 0 := by
  have hb:∀c d:Fin r,Ω (blockLabels u (SquarefreeBlocks.blocks b κ) c)
      (blockLabels u (SquarefreeBlocks.blocks b κ) d)=
      ∑i∈Finset.univ.filter (fun i=>κ i=c),∑j∈Finset.univ.filter (fun j=>κ j=d),Ω (u (b i)) (u (b j)) := by
    intro c d
    simp only [blockLabels,SquarefreeBlocks.blocks,Finset.sum_map,map_sum,AddMonoidHom.finsetSum_apply]
    rw [Finset.sum_comm]
  rw [wordEnergy_eq_pairs]
  simp only [hb]
  calc
    (∑c:Fin r,∑d:Fin r,if c<d then
      ∑i∈Finset.univ.filter (fun i=>κ i=c),∑j∈Finset.univ.filter (fun j=>κ j=d),Ω (u (b i)) (u (b j)) else 0)=
      ∑c:Fin r,∑d:Fin r,∑i:Fin n,∑j:Fin n,
        if κ i=c ∧ κ j=d ∧ c<d then Ω (u (b i)) (u (b j)) else 0 := by
          apply Finset.sum_congr rfl
          intro c hc
          apply Finset.sum_congr rfl
          intro d hd
          by_cases h:c<d
          · simp only [h,ite_true, if_true,Finset.sum_filter,ite_and]
            apply Finset.sum_congr rfl
            intro i hi
            by_cases hh:κ i=c <;> simp [hh]
          · simp [h]
    _ = ∑i:Fin n,∑j:Fin n,∑c:Fin r,∑d:Fin r,
        if κ i=c ∧ κ j=d ∧ c<d then Ω (u (b i)) (u (b j)) else 0 := by
          calc
            _ = ∑c:Fin r,∑i:Fin n,∑d:Fin r,∑j:Fin n,
                if κ i=c ∧ κ j=d ∧ c<d then Ω (u (b i)) (u (b j)) else 0 := by
                  apply Finset.sum_congr rfl
                  intro c hc
                  rw [Finset.sum_comm]
            _ = ∑i:Fin n,∑c:Fin r,∑d:Fin r,∑j:Fin n,
                if κ i=c ∧ κ j=d ∧ c<d then Ω (u (b i)) (u (b j)) else 0 :=
                  Finset.sum_comm
            _ = _ := by
              apply Finset.sum_congr rfl
              intro i hi
              calc
                _ = ∑c:Fin r,∑j:Fin n,∑d:Fin r,
                    if κ i=c ∧ κ j=d ∧ c<d then Ω (u (b i)) (u (b j)) else 0 := by
                      apply Finset.sum_congr rfl
                      intro c hc
                      rw [Finset.sum_comm]
                _ = _ := Finset.sum_comm
    _ = _ := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          simp [ite_and,Finset.sum_ite_irrel]
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
local instance polynomialAdjointCoefficientsAddCommMonoid_r90e676_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance polynomialAdjointCoefficientsAddGroup_r90e676_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
lemma actualPolynomialAdjointCoefficient_add (τ:M →+ ℤ) (f:PowerSeries (Torus LaurentRay.vUnit Ω))
    (F G:Torus LaurentRay.vUnit Ω) (m:M) :
    actualPolynomialAdjointCoefficient Ω τ f (F+G) m=
      actualPolynomialAdjointCoefficient Ω τ f F m+actualPolynomialAdjointCoefficient Ω τ f G m := by
  exact Finsupp.sum_add_index' (fun _=>zero_mul _) (fun _ _ _=>add_mul _ _ _)

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Histories_CommonHistoryLeaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus.LocalHistoryFormula
open PowerSeries PowerSeriesAdjoint PowerSeriesSplit LaurentPositive WallUnits
open scoped BigOperators
open Classical
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]

variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M) (e:M →+ E)
variable (F:CompletedPositive LaurentRay.vUnit Ω C)

lemma leafBound (b:M) (N:ℕ) (p:LocalHistoryFormula M E) (hp:p.Bounded C b N) (l:p.Leaf) :
    p.leafDegree l≤N ∧ HasRootDegree C (p.leafDegree l) (p.leafExponent l-b) := by
  induction p generalizing N with
  | zero=>exact l.elim
  | stop j m=>exact hp
  | add p q ihp ihq=>cases l with
    | inl l=>exact ihp N hp.1 l
    | inr l=>exact ihq N hp.2 l
  | jump d m r t p ih=>
    obtain ⟨hd,j,hj,hp⟩:=hp
    obtain ⟨hl,hr⟩:=ih j hp l
    exact ⟨by dsimp [leafDegree]; omega,hr⟩

end
end ElementaryPositivity.QuantumTorus.LocalHistoryFormula

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_OrbitMonomialSymmetric
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq _root_.OAI.ElementaryPositivity.TriangularDynamics.instAntisymmCellPhaseLE _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
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

lemma coeff_polynomial (μ d:σ →₀ ℕ) : (polynomial μ: MvPolynomial σ R).coeff d=
    if d∈exponentOrbit μ then 1 else 0 := by
  simp [polynomial,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial,eq_comm]

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

end
end ElementaryPositivity.OrbitMonomial

end
section
namespace ElementaryPositivity.OrbitMonomial
open scoped BigOperators
open Classical
noncomputable section
variable {σ:Type*} [Fintype σ] [DecidableEq σ] {R:Type*} [CommRing R]

lemma exponentOrbit_symm {μ d:σ →₀ ℕ} (h:d∈exponentOrbit μ) : μ∈exponentOrbit d := by
  obtain ⟨e,_,rfl⟩:=Finset.mem_image.mp h
  have H:=exponentOrbit_map (μ.mapDomain e) e.symm _ (exponentOrbit_self _)
  simpa only [←Finsupp.mapDomain_comp,Equiv.symm_comp_self,Finsupp.mapDomain_id] using H
lemma exponentOrbit_trans {μ d k:σ →₀ ℕ} (hd:d∈exponentOrbit μ) (hk:k∈exponentOrbit d) :
    k∈exponentOrbit μ := by
  obtain ⟨e,_,rfl⟩:=Finset.mem_image.mp hk
  exact exponentOrbit_map μ e d hd
lemma symmetric_coeff_orbit (p:MvPolynomial σ R) (hp:p.IsSymmetric) (μ d:σ →₀ ℕ)
    (hd:d∈exponentOrbit μ) : p.coeff d=p.coeff μ := by
  obtain ⟨e,_,rfl⟩:=Finset.mem_image.mp hd
  have H := MvPolynomial.coeff_rename_mapDomain e e.injective p μ
  simpa only [hp e] using H

lemma dominant_representative {n:ℕ} (d:Fin (n+1) →₀ ℕ) :
    ∃μ:Fin (n+1) →₀ ℕ,(∀i:Fin n,μ i.succ ≤ μ i.castSucc) ∧ d∈exponentOrbit μ := by
  let e:Equiv.Perm (Fin (n+1)):=Tuple.sort (α:=OrderDual ℕ) (fun i=>d i)
  let μ:=d.mapDomain e.symm
  have H:∀i,μ i=d (e i):=by
    intro i
    simpa only [μ,Equiv.symm_apply_apply] using (Finsupp.mapDomain_apply e.symm.injective d (e i))
  refine ⟨μ,?_,exponentOrbit_symm (exponentOrbit_map d e.symm d (exponentOrbit_self d))⟩
  intro i
  rw [H,H]
  have hm := Tuple.monotone_sort (α:=OrderDual ℕ) (fun j : Fin (n+1) => d j)
  exact hm (Fin.castSucc_le_succ i)

lemma symmetric_orbit_decomposition {n:ℕ} (p:MvPolynomial (Fin (n+1)) R) (hp:p.IsSymmetric) :
    p=∑μ∈p.support.filter (fun μ=>∀i:Fin n,μ i.succ ≤ μ i.castSucc),
      MvPolynomial.C (p.coeff μ)*polynomial μ := by
  apply MvPolynomial.ext
  intro d
  obtain ⟨μ,hμ,hd⟩:=dominant_representative d
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_C_mul,coeff_polynomial]
  symm
  rw [Finset.sum_eq_single μ]
  · rw [ite_eq_left hd,mul_one]
    exact (symmetric_coeff_orbit p hp μ d hd).symm
  · intro ν hν hne
    obtain ⟨_,hν⟩:=Finset.mem_filter.mp hν
    have hn:d∉exponentOrbit ν:=by
      intro hv
      exact hne (dominant_orbit_unique μ ν hμ hν (exponentOrbit_trans hd (exponentOrbit_symm hv)))
    rw [ite_eq_right hn,mul_zero]
  · intro h
    have hh:p.coeff μ=0:=by
      by_contra hh
      exact h (Finset.mem_filter.mpr ⟨MvPolynomial.mem_support_iff.mpr hh,hμ⟩)
    rw [hh,zero_mul]
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

omit [Fintype V] in
lemma includeVertices_injective : Function.Injective (includeVertices (V:=V)) := by
  intro a b h
  exact congrArg Prod.fst h
end ElementaryPositivity.LatticeExtension

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_CovectorPrescriptions
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RawShuffle.quotientAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
attribute [-simp] _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (C:(I → ℤ) →+ M) (e:M →+ E)
lemma real_covector_prescribe (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i))) (w:I → ℝ) :
    ∃J:Module.Dual ℝ E,∀i,J (e (simpleRoot C i))=w i := by
  classical
  obtain ⟨D,hD⟩:=realRootCoordinates_exists C e hC
  refine ⟨∑i,w i • (LinearMap.proj i).comp D,fun i=>?_⟩
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply,
    real_coordinate_simple C e D hD,LinearMap.proj_apply,smul_eq_mul,Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji; simp [hji]
  · simp
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
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus LatticeExtension LatticeRealization
open Classical
noncomputable section
variable {n:ℕ}

lemma extendedOmega_self : ∀m,extendedOmega n m m=0 := form_self _ triangularOmega_self
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
local instance instAddCommMonoidTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega_2_r90e676_1 : AddCommMonoid (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommMonoid
local instance instAddCommGroupTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega_2_r90e676_1 : AddCommGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommGroup
local instance instAddGroupTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega_2_r90e676_1 : AddGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddGroup
local instance instSubTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega_2_r90e676_1 : Sub (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toSub
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
local instance triangularAnchorProjectionSub_r90e676_1 : Sub (Torus LaurentRay.vUnit (extendedOmega n)) :=
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
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_ExpressionAdditiveOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open scoped BigOperators
noncomputable section

variable {σ:Type*} [Fintype σ] {R:Type*} [CommRing R]
lemma ElementaryExpr.ordinary_nscale {N:ℕ} (f:ElementaryExpr N) (k:ℕ) :
    (nscale k f).ordinary (σ:=σ) (R:=R)=k • f.ordinary := by
  induction k with
  | zero=>simp [nscale,ordinary]
  | succ k ih=>simp only [nscale,ordinary,ih,add_nsmul,one_nsmul]
lemma ElementaryExpr.ordinary_zscale {N:ℕ} (f:ElementaryExpr N) (z:ℤ) :
    (zscale z f).ordinary (σ:=σ) (R:=R)=z • f.ordinary := by
  cases z with
  | ofNat k=>simpa [zscale] using ordinary_nscale (σ:=σ) (R:=R) f k
  | negSucc k=>simp only [zscale,ordinary,ordinary_nscale,negSucc_zsmul]
lemma ElementaryExpr.ordinary_symmetric {N:ℕ} (f:ElementaryExpr N) :
    (f.ordinary (σ:=σ) (R:=R)).IsSymmetric := by
  induction f with
  | zero=>intro e; exact map_zero _
  | one=>intro e; exact map_one _
  | atom k=>exact MvPolynomial.esymm_isSymmetric σ R k
  | add f g hf hg=>intro e; simp only [ordinary,map_add,hf e,hg e]
  | neg f hf=>intro e; simp only [ordinary,map_neg,hf e]
  | mul f g hf hg=>intro e; simp only [ordinary,map_mul,hf e,hg e]
end
end ElementaryPositivity.QuantumTorus
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension LatticeRealization PowerSeries PowerSeriesAdjoint
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}

local instance expressionAdditiveOperationsRing_r90e676_1 : Ring (Torus LaurentRay.vUnit (extendedOmega n)) := Torus.instRing LaurentRay.vUnit (extendedOmega n)
local instance expressionAdditiveOperationsAddCommMonoid_r90e676_1 : AddCommMonoid (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommMonoid
local instance expressionAdditiveOperationsAddCommGroup_r90e676_1 : AddCommGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommGroup
local instance expressionAdditiveOperationsAddGroup_r90e676_1 : AddGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddGroup
local instance expressionAdditiveOperationsSub_r90e676_1 : Sub (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toSub
lemma triangularExpression_ordinary_equal {N:ℕ} (f g:ElementaryExpr N)
    (h:f.ordinary (σ:=Fin (n+1)) (R:=ℤ)=g.ordinary) : triangularExpression (n:=n) f=triangularExpression g := by
  have h':f.ordinary (σ:=Fin (n+1)) (R:=LaurentSeries ℚ)=g.ordinary:=by
    rw [←ElementaryExpr.ordinary_map f (Int.castRingHom _),h,ElementaryExpr.ordinary_map]
  apply triangularPure_equal
  intro μ
  by_cases hn:∀a,0≤μ a
  · let d:Fin (n+1) →₀ ℕ:=Finsupp.equivFunOnFinite.symm (fun a=>(μ a).toNat)
    have hd:∀a,(d a:ℤ)=μ a:=fun a=>Int.toNat_of_nonneg (hn a)
    have he:includeVertices (pureAnchor μ)=anchorExponent d:=by
      change includeVertices (pureAnchor μ)=includeVertices (pureAnchor (fun a=>(d a:ℤ)))
      rw [show (fun a=>(d a:ℤ))=μ from funext hd]
    rw [he,triangularExpression_anchorCoeff,triangularExpression_anchorCoeff,h']
  · obtain ⟨a,ha⟩:=not_forall.mp hn
    have hz:∀e:ElementaryExpr N,triangularExpression e (includeVertices (pureAnchor μ))=0:=by
      intro e
      by_contra hh
      have H:0≤pureAnchor μ (.inl a):=triangularSeed_nonneg e _ (Finsupp.mem_support_iff.mpr hh) (.inl a)
      exact ha (by simpa only [pureAnchor_apply_anchor] using H)
    rw [hz,hz]
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

lemma triangularIncoming_zero (N : ℕ) (m : Lattice n (Cell n)) :
    triangularIncoming (.zero N) m = 0 := by
  simp [triangularIncoming,triangularExpression,ElementaryExpr.eval,polynomialSectionIncoming,
    polynomialSectionCoefficient,actualPolynomialAdjointCoefficient]
lemma triangularIncoming_add {N : ℕ} (f g : ElementaryExpr N) (m : Lattice n (Cell n)) :
    triangularIncoming (.add f g) m = triangularIncoming f m + triangularIncoming g m :=
  actualPolynomialAdjointCoefficient_add _ _ _ _ _ _
lemma triangularIncoming_neg {N : ℕ} (f : ElementaryExpr N) (m : Lattice n (Cell n)) :
    triangularIncoming (.neg f) m = -triangularIncoming f m := by
  have H := triangularIncoming_add f (.neg f) m
  have hz : triangularIncoming (.add f (.neg f)) m = 0 := by
    change actualPolynomialAdjointCoefficient _ _ _ (triangularExpression f + -triangularExpression f) _ = 0
    rw [add_neg_cancel]
    simp [actualPolynomialAdjointCoefficient]
  rw [hz] at H
  exact eq_neg_of_add_eq_zero_right H.symm

lemma AnchorSupported.zero (N:ℕ) : AnchorSupported (n:=n) (.zero N) := by
  intro m h; exact (h (triangularIncoming_zero N m)).elim
lemma AnchorSupported.add {N:ℕ} {f g:ElementaryExpr N}
    (hf:AnchorSupported (n:=n) f) (hg:AnchorSupported (n:=n) g) :
    AnchorSupported (n:=n) (.add f g) := by
  intro m hm
  rw [triangularIncoming_add] at hm
  by_cases h:triangularIncoming f m=0
  · rw [h,zero_add] at hm; exact hg m hm
  · exact hf m h
lemma AnchorSupported.neg {N:ℕ} {f:ElementaryExpr N} (hf:AnchorSupported (n:=n) f) :
    AnchorSupported (n:=n) (.neg f) := by
  intro m hm
  rw [triangularIncoming_neg] at hm
  exact hf m (fun h=>hm (by rw [h,neg_zero]))
lemma AnchorSupported.nscale {N:ℕ} {f:ElementaryExpr N} (hf:AnchorSupported (n:=n) f) (k:ℕ) :
    AnchorSupported (n:=n) (f.nscale k) := by
  induction k with
  | zero=>exact AnchorSupported.zero N
  | succ k ih=>exact ih.add hf
lemma AnchorSupported.zscale {N:ℕ} {f:ElementaryExpr N} (hf:AnchorSupported (n:=n) f) (z:ℤ) :
    AnchorSupported (n:=n) (f.zscale z) := by
  cases z with
  | ofNat k=>exact hf.nscale k
  | negSucc k=>exact (hf.nscale (k+1)).neg

lemma triangularExpression_anchorSupported {N:ℕ} (f:ElementaryExpr N) : AnchorSupported (n:=n) f := by
  let p:MvPolynomial (Fin (n+1)) ℤ:=f.ordinary
  let s:=p.support.filter (fun μ=>∀i:Fin n,μ i.succ ≤ μ i.castSucc)
  have ht:∀μ∈s,∃g:ElementaryExpr N,
      g.ordinary=MvPolynomial.C (p.coeff μ)*OrbitMonomial.polynomial μ ∧ AnchorSupported (n:=n) g:=by
    intro μ hμ
    obtain ⟨hmem,hdom⟩:=Finset.mem_filter.mp hμ
    have hdeg:μ.degree=N:=by
      by_contra h
      exact (MvPolynomial.mem_support_iff.mp hmem) (f.ordinary_homogeneous.coeff_eq_zero h)
    obtain ⟨g,hg,hs⟩:=monomial_producer_supported μ hdom
    let g':ElementaryExpr N:=hdeg ▸ g
    have ho:g'.ordinary=(OrbitMonomial.polynomial μ:MvPolynomial (Fin (n+1)) ℤ):=by
      rw [ElementaryExpr.ordinary_cast]; exact hg
    have hs':AnchorSupported (n:=n) g':=by
      subst N; exact hs
    refine ⟨g'.zscale (p.coeff μ),?_,hs'.zscale _⟩
    rw [ElementaryExpr.ordinary_zscale,ho,zsmul_eq_mul]
    congr 1
  have hw:∀t:Finset (Fin (n+1) →₀ ℕ),t⊆s → ∃g:ElementaryExpr N,
      g.ordinary=∑μ∈t,MvPolynomial.C (p.coeff μ)*OrbitMonomial.polynomial μ ∧ AnchorSupported (n:=n) g:=by
    intro t
    induction t using Finset.induction with
    | empty=>intro _; exact ⟨.zero N,by simp [ElementaryExpr.ordinary],AnchorSupported.zero N⟩
    | @insert μ t hμ ih=>
      intro h
      obtain ⟨g,hg,hs⟩:=ht μ (h (Finset.mem_insert_self _ _))
      obtain ⟨g',hg',hs'⟩:=ih (fun a ha=>h (Finset.mem_insert_of_mem ha))
      refine ⟨.add g g',?_,hs.add hs'⟩
      change g.ordinary+g'.ordinary=_
      rw [hg,hg',Finset.sum_insert hμ]
  obtain ⟨g,hg,hs⟩:=hw s (fun _=>id)
  have hp:p=∑μ∈s,MvPolynomial.C (p.coeff μ)*OrbitMonomial.polynomial μ:=
    OrbitMonomial.symmetric_orbit_decomposition p f.ordinary_symmetric
  have he:triangularExpression (n:=n) f=triangularExpression g:=
    triangularExpression_ordinary_equal f g (hp.trans hg.symm)
  intro m hm
  have hi:triangularIncoming f m=triangularIncoming g m:=by unfold triangularIncoming; rw [he]
  rw [hi] at hm
  exact hs m hm
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

lemma rootCone_dual_zero (N d:ℕ) (m:Extended (Vertex n (Cell n)))
    (hm:HasRootDegree (extendedRoots n) d (m-triangularBase N)) : m.2=0 := by
  obtain ⟨c,hc,he⟩:=hm
  have H:=congrArg Prod.snd he
  change (0:Lattice n (Cell n))=m.2-0 at H
  simpa using H.symm

lemma leafProfile_dominant {E:Type*} [AddCommGroup E] [Module ℝ E] (N:ℕ)
    (p:LocalHistoryFormula (Extended (Vertex n (Cell n))) E)
    (l:{l:p.Leaf // AnchoredLeaf N p l}) : ∀i:Fin n,leafProfile N p l i.succ≤leafProfile N p l i.castSucc :=
  l.property.choose_spec.2.1
lemma leafProfile_exponent {E:Type*} [AddCommGroup E] [Module ℝ E] (N:ℕ)
    (p:LocalHistoryFormula (Extended (Vertex n (Cell n))) E)
    (l:{l:p.Leaf // AnchoredLeaf N p l}) : p.leafExponent l.val=anchorExponent (leafProfile N p l) :=
  l.property.choose_spec.2.2

lemma triangular_common_history (N d:ℕ) (r:Extended (Vertex n (Cell n)))
    (hr:HasRootDegree (extendedRoots n) d (r-triangularBase N)) :
    ∃p:LocalHistoryFormula (Extended (Vertex n (Cell n)))
      ((Vertex n (Cell n) → ℝ) × (Vertex n (Cell n) → ℝ)),
      p.Positive (extendedOmega n) (extendedRoots n) extendedCast
        (simpleTotalTransport (extendedOmega n) (extendedRoots n)) ∧
      p.Bounded (extendedRoots n) (triangularBase N) d ∧
      ∀f:ElementaryExpr N, triangularExpression f r=
        ∑l:{l:p.Leaf // AnchoredLeaf N p l},
          p.leafWeight (extendedOmega n) (extendedRoots n) extendedCast
            (simpleTotalTransport (extendedOmega n) (extendedRoots n)) l.val *
          (f.ordinary (σ:=Fin (n+1)) (R:=LaurentSeries ℚ)).coeff (leafProfile N p l) := by
  obtain ⟨L,hL⟩:=real_covector_prescribe (extendedRoots n) extendedCast extendedRoots_realIndependent (fun _=>1)
  obtain ⟨p,hp,hb,he⟩:=polynomial_common_history (extendedOmega n) extendedOmega_self
    (extendedRoots n) (extendedCoord n) extendedCoord_roots extendedCast extendedCast_injective
    (triangularRealForm n) triangularRealForm_self triangularRealForm_compatible L
    (fun _ _ hm=>covector_root_eval (extendedRoots n) extendedCast L hL hm)
    (triangularBase N) (triangularBase_order N) d r hr
  refine ⟨p,hp,hb,?_⟩
  intro f
  rw [he (triangularExpression f) (fun m hm=>triangularSeed_in_rootCone f m (Finsupp.mem_support_iff.mpr hm))]
  have hz:∀l:p.Leaf,¬AnchoredLeaf N p l →
      polynomialSectionIncoming (extendedOmega n) (extendedRoots n) (extendedCoord n)
        (triangularExpression f) (p.leafExponent l)=0 := by
    intro l ha
    by_contra hh
    have hd:=rootCone_dual_zero N (p.leafDegree l) (p.leafExponent l) (p.leafBound _ _ _ hb l).2
    have hm:p.leafExponent l=includeVertices (p.leafExponent l).1:=Prod.ext rfl hd
    rw [hm] at hh
    obtain ⟨μ,hμ,hdom,hlabel⟩:=triangularExpression_anchorSupported f _ hh
    apply ha
    exact ⟨μ,hμ,hdom,hm.trans (congrArg includeVertices hlabel)⟩
  rw [←Fintype.sum_subtype_add_sum_subtype (AnchoredLeaf N p)]
  have hn:(∑l:{l:p.Leaf // ¬AnchoredLeaf N p l},
      p.leafWeight (extendedOmega n) (extendedRoots n) extendedCast
        (simpleTotalTransport (extendedOmega n) (extendedRoots n)) l.val *
      polynomialSectionIncoming (extendedOmega n) (extendedRoots n) (extendedCoord n)
        (triangularExpression f) (p.leafExponent l.val))=0 := by
    apply Finset.sum_eq_zero
    intro l hl
    rw [hz l.val l.property,mul_zero]
  rw [hn,add_zero]
  apply Finset.sum_congr rfl
  intro l hl
  congr 1
  rw [leafProfile_exponent N p l]
  exact triangularIncoming_anchorCoeff f _ (leafProfile_dominant N p l)
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_GraphBlockPairing
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instAddCommGroup _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
attribute [-simp] _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity
open scoped BigOperators
open Classical
noncomputable section

lemma ordered_pair_sum {n:ℕ} (f:Fin n → Fin n → ℤ) (hf:∀i,f i i=0) :
    (∑i:Fin n,∑j:Fin n,f i j) = ∑i:Fin n,∑j:Fin n,if i < j then f i j+f j i else 0 := by
  have H:(∑i:Fin n,∑j:Fin n,f i j)=(∑i:Fin n,∑j:Fin n,if i < j then f i j else 0)+(∑i:Fin n,∑j:Fin n,if j < i then f i j else 0) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rcases lt_trichotomy i j with h|h|h
    · simp [h,not_lt_of_gt h]
    · subst j; simp [hf]
    · simp [h,not_lt_of_gt h]
  rw [H,Finset.sum_comm (f:=fun i j=>if j < i then f i j else 0),←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> simp

namespace NaturalUnitIntervalGraph
open QuantumTorus
variable {n r:ℕ} (G:NaturalUnitIntervalGraph n)
variable {M V:Type*} [AddCommGroup M] [Fintype V] [DecidableEq V]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0) (u:V → M) (b:Fin n ↪ V)
variable (hp:∀i j,i < j → Ω (u (b i)) (u (b j))= -(if G.Edge i j then 1 else 0))

include hΩ hp in
omit [Fintype V] [DecidableEq V] in
lemma pairing_zero_iff (i j:Fin n) : Ω (u (b i)) (u (b j))=0 ↔ ¬G.Edge i j := by
  rcases lt_trichotomy i j with h|h|h
  · rw [hp i j h]
    by_cases he:G.Edge i j <;> simp [he]
  · subst j; simp [hΩ]
  · rw [QuantumTorus.alternating_skew Ω hΩ, hp j i h,G.edge_comm i j]
    simp

include hΩ hp in
omit [Fintype V] [DecidableEq V] in
lemma independent_blocks_iff (κ:Fin n → Fin r) :
    (∀c,IsIndependent Ω u (SquarefreeBlocks.blocks b κ c)) ↔ G.Proper κ := by
  constructor
  · intro h i j he heq
    have H:=h (κ i) (b i) ((SquarefreeBlocks.mem_blocks b κ _ _).mpr ⟨i,rfl,rfl⟩)
      (b j) ((SquarefreeBlocks.mem_blocks b κ _ _).mpr ⟨j,heq.symm,rfl⟩)
    exact ((G.pairing_zero_iff Ω hΩ u b hp i j).mp H) he
  · intro h c x hx y hy
    obtain ⟨i,hi,rfl⟩:=(SquarefreeBlocks.mem_blocks b κ c x).mp hx
    obtain ⟨j,hj,rfl⟩:=(SquarefreeBlocks.mem_blocks b κ c y).mp hy
    apply (G.pairing_zero_iff Ω hΩ u b hp i j).mpr
    exact fun he=>h i j he (hi.trans hj.symm)

include hΩ hp in
omit [Fintype V] [DecidableEq V] in
lemma blockValid_iff (κ:Fin n → Fin r) (a:Fin r → ℕ) :
    BlockValid Ω u a (SquarefreeBlocks.blocks b κ) ↔
      G.Proper κ ∧ ∀c,(Finset.univ.filter (fun i=>κ i=c)).card=a c := by
  rw [BlockValid,forall_and,G.independent_blocks_iff Ω hΩ u b hp]
  simp only [SquarefreeBlocks.blocks,Finset.card_map]

include hΩ hp in
omit [Fintype V] [DecidableEq V] in
lemma blocks_energy (κ:Fin n → Fin r) (hκ:G.Proper κ) :
    wordEnergy Ω (blockLabels u (SquarefreeBlocks.blocks b κ))=
      2*(G.coloringInversions κ:ℤ)-(G.edgeCount:ℤ) := by
  rw [wordEnergy_blocks,ordered_pair_sum _ (by intro i; simp)]
  have H:∀i j:Fin n,(if i < j then
      (if κ i<κ j then Ω (u (b i)) (u (b j)) else 0)+
      (if κ j<κ i then Ω (u (b j)) (u (b i)) else 0) else 0)=
      (if i < j ∧ G.Edge i j ∧ κ j<κ i then (1:ℤ) else 0)-
      (if i < j ∧ G.Edge i j ∧ κ i<κ j then (1:ℤ) else 0) := by
    intro i j
    by_cases hij:i < j
    · rw [ite_eq_left hij,QuantumTorus.alternating_skew Ω hΩ (u (b j)) (u (b i)),hp i j hij]
      by_cases he:G.Edge i j
      · rcases lt_or_gt_of_ne (hκ i j he) with h|h
        · simp [hij,he,h,not_lt_of_gt h]
        · simp [hij,he,h,not_lt_of_gt h]
      · simp [hij,he]
    · simp [hij]
  simp only [H,Finset.sum_sub_distrib]
  have hi:(G.coloringInversions κ:ℤ)=
      ∑i:Fin n,∑j:Fin n,if i < j ∧ G.Edge i j ∧ κ j<κ i then (1:ℤ) else 0 := by
    simp only [coloringInversions,edges,Finset.filter_filter,Finset.card_eq_sum_ones,
      Nat.cast_sum,Finset.sum_filter,Fintype.sum_prod_type,apply_ite,Nat.cast_one,Nat.cast_zero]
    congr 2
    funext i
    congr 1
    funext j
    simp [and_assoc]
  have ha:(G.coloringAscents κ:ℤ)=
      ∑i:Fin n,∑j:Fin n,if i < j ∧ G.Edge i j ∧ κ i<κ j then (1:ℤ) else 0 := by
    simp only [coloringAscents,Finset.card_eq_sum_ones,
      Nat.cast_sum,Finset.sum_filter,Fintype.sum_prod_type,apply_ite,Nat.cast_one,Nat.cast_zero]
  rw [←hi,←ha]
  have hc: (G.coloringInversions κ:ℤ)+(G.coloringAscents κ:ℤ)=(G.edgeCount:ℤ):=by
    exact_mod_cast G.coloringInversions_add_ascents κ hκ
  omega
end NaturalUnitIntervalGraph
end
end ElementaryPositivity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_GraphSquarefreeKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.NaturalUnitIntervalGraph
open QuantumTorus
open scoped BigOperators
open Classical
noncomputable section
variable {n r:ℕ} (G:NaturalUnitIntervalGraph n)
variable {K M V:Type*} [Field K] [AddCommGroup M] [Fintype V] [DecidableEq V]
variable (v:Kˣ) (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (c:(V → ℤ) →+ M) (hc:Function.Injective c) (b:Fin n ↪ V)
variable (hp:∀i j,i < j → Ω (c (Pi.single (b i) 1)) (c (Pi.single (b j) 1))= -(if G.Edge i j then 1 else 0))

local instance graphSquarefreeKernelRing_r90e676_1 : Ring (Torus v Ω) := Torus.instRing v Ω
include hΩ hc hp in
lemma graph_squarefree_kernel (a:Fin r → ℕ) :
    ((List.ofFn (fun i=>independentElement v Ω (fun x=>c (Pi.single x 1)) (a i))).prod)
        (c (SquarefreeBlocks.target b))=
      ∑κ:Fin n → Fin r,
        if G.Proper κ ∧ (∀i,(Finset.univ.filter (fun j=>κ j=i)).card=a i) then
          ↑(v^(2*(G.coloringInversions κ:ℤ)-(G.edgeCount:ℤ))) else 0 := by
  rw [independent_product_squarefree v Ω c hc b]
  apply Finset.sum_congr rfl
  intro κ hκ
  rw [G.blockValid_iff Ω hΩ _ b hp]
  split_ifs with h
  · rw [G.blocks_energy Ω hΩ _ b hp κ h.1]
  · rfl
end
end ElementaryPositivity.NaturalUnitIntervalGraph

end
section
namespace ElementaryPositivity.QuantumTorus
open scoped BigOperators
open Classical
noncomputable section

variable {M V:Type*} [AddCommGroup M] [Fintype V] [DecidableEq V]
variable (v:(LaurentSeries ℚ)ˣ) (Ω:M →+ M →+ ℤ)
local instance graphSquarefreeSequenceRing_r90e676_1 : Ring (Torus v Ω) := Torus.instRing v Ω
lemma ElementaryExpr.sequence_eval (u:V → M) (a:List ℕ) :
    (sequence a).eval v Ω u=(a.map (independentElement v Ω u)).prod := by
  induction a with
  | nil=>rfl
  | cons k a ih=>change independentElement v Ω u k*(sequence a).eval v Ω u=_; rw [ih]; rfl
lemma ElementaryExpr.eval_cast {N K:ℕ} (h:N=K) (f:ElementaryExpr N) (u:V → M) :
    (h ▸ f).eval v Ω u=f.eval v Ω u := by subst K; rfl
variable {R σ:Type*} [CommRing R] [Fintype σ]
lemma ElementaryExpr.sequence_ordinary (a:List ℕ) :
    (sequence a).ordinary (σ:=σ) (R:=R)=(a.map (MvPolynomial.esymm σ R)).prod := by
  induction a with
  | nil=>rfl
  | cons k a ih=>change MvPolynomial.esymm σ R k*(sequence a).ordinary=_; rw [ih]; rfl

lemma ElementaryExpr.sequence_ofFn_eval (u:V → M) {r:ℕ} (a:Fin r → ℕ) :
    (sequence (List.ofFn a)).eval v Ω u=(List.ofFn (fun i=>independentElement v Ω u (a i))).prod := by
  rw [sequence_eval,List.map_ofFn]
  rfl
lemma ElementaryExpr.sequence_ofFn_ordinary {r:ℕ} (a:Fin r → ℕ) :
    (sequence (List.ofFn a)).ordinary (σ:=σ) (R:=R)=∏i:Fin r,MvPolynomial.esymm σ R (a i) := by
  rw [sequence_ordinary,List.map_ofFn,List.prod_ofFn]
  rfl
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RationalIntervalModel
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq
attribute [-simp] _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity
open scoped BigOperators

lemma rational_finite_between (s t:Finset ℚ) (h:∀a∈s,∀b∈t,a < b) :
    ∃x:ℚ,(∀a∈s,a < x) ∧ ∀b∈t,x < b := by
  classical
  by_cases hs:s.Nonempty
  · let a:=s.max' hs
    by_cases ht:t.Nonempty
    · let b:=t.min' ht
      obtain ⟨x,hax,hxb⟩:=exists_between (h a (s.max'_mem hs) b (t.min'_mem ht))
      exact ⟨x,fun c hc=>(s.le_max' c hc).trans_lt hax,fun c hc=>hxb.trans_le (t.min'_le c hc)⟩
    · refine ⟨a+1,fun c hc=>(s.le_max' c hc).trans_lt (lt_add_one a),?_⟩
      simp [Finset.not_nonempty_iff_eq_empty.mp ht]
  · by_cases ht:t.Nonempty
    · let b:=t.min' ht
      refine ⟨b-1,?_,fun c hc=>(sub_one_lt b).trans_le (t.min'_le c hc)⟩
      simp [Finset.not_nonempty_iff_eq_empty.mp hs]
    · exact ⟨0,by simp [Finset.not_nonempty_iff_eq_empty.mp hs],by simp [Finset.not_nonempty_iff_eq_empty.mp ht]⟩

lemma rational_interval_prefix (h:ℕ → ℕ) (hh:Monotone h) (m:ℕ) :
    ∃t:ℕ → ℚ,(∀i  <  m,0 < t i) ∧
      ∀i j,i < j → j < m → t i < t j ∧
        (j≤h i → t j < t i+1) ∧ (h i < j → t i+1 < t j) := by
  classical
  induction m with
  | zero=>exact ⟨fun _=>1,by simp,by omega⟩
  | succ m ih=>
    obtain ⟨t,ht,he⟩:=ih
    let lower:Finset ℚ:={0} ∪ (Finset.range m).image t ∪
      ((Finset.range m).filter (fun i=>h i < m)).image (fun i=>t i+1)
    let upper:Finset ℚ:=((Finset.range m).filter (fun i=>m≤h i)).image (fun i=>t i+1)
    have hcross:∀a∈lower,∀b∈upper,a < b:=by
      intro a ha b hb
      obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hb
      obtain ⟨hjm,hjh⟩:=Finset.mem_filter.mp hj
      have hjm':j < m:=Finset.mem_range.mp hjm
      rcases Finset.mem_union.mp ha with ha|ha
      · rcases Finset.mem_union.mp ha with ha|ha
        · have ha:a=0:=Finset.mem_singleton.mp ha
          rw [ha]
          linarith [ht j hjm']
        · obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp ha
          have him:i < m:=Finset.mem_range.mp hi
          rcases lt_trichotomy i j with hij|rfl|hji
          · linarith [(he i j hij hjm').1]
          · exact lt_add_one _
          · exact (he j i hji him).2.1 (le_trans (Nat.le_of_lt him) hjh)
      · obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp ha
        obtain ⟨him,hih⟩:=Finset.mem_filter.mp hi
        have hij:i < j:=by
          by_contra hn
          have H:=hh (Nat.le_of_not_gt hn)
          omega
        linarith [(he i j hij hjm').1]
    obtain ⟨x,hxL,hxU⟩:=rational_finite_between lower upper hcross
    have hx0:0 < x:=hxL 0 (by simp [lower])
    have hxt:∀i  <  m,t i < x:=by
      intro i hi
      apply hxL
      simp only [lower,Finset.mem_union]
      exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr hi,rfl⟩))
    have hxadj:∀i  <  m,m≤h i → x < t i+1:=by
      intro i hi hh
      apply hxU
      exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,hh⟩,rfl⟩
    have hxnon:∀i  <  m,h i < m → t i+1 < x:=by
      intro i hi hh
      apply hxL
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,hh⟩,rfl⟩))
    refine ⟨Function.update t m x,?_,?_⟩
    · intro i hi
      by_cases him:i=m
      · simpa [him] using hx0
      · rw [Function.update_of_ne him]
        exact ht i (by omega)
    · intro i j hij hj
      have him:i≠m:=by omega
      rw [Function.update_of_ne him]
      by_cases hjm:j=m
      · subst j
        rw [Function.update_self]
        exact ⟨hxt i hij,hxadj i hij,hxnon i hij⟩
      · rw [Function.update_of_ne hjm]
        exact he i j hij (by omega)
end ElementaryPositivity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_GraphRationalModel
attribute [-instance] _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
attribute [-simp] _root_.OAI.ElementaryPositivity.NaturalUnitIntervalGraph.edge_comm _root_.OAI.ElementaryPositivity.NaturalUnitIntervalGraph.edge_irrefl _root_.OAI.ElementaryPositivity.NaturalUnitIntervalGraph.mem_edges _root_.OAI.ElementaryPositivity.NaturalUnitIntervalGraph.mem_invertedEdges _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.NaturalUnitIntervalGraph
variable {n:ℕ} (G:ElementaryPositivity.NaturalUnitIntervalGraph n)

lemma extendedH_monotone : Monotone G.extendedH := by
  intro i j hij
  unfold extendedH
  split_ifs with hi hj
  · exact G.increasing hij
  · have hv: (G.h ⟨i,hi⟩).val < n := (G.h ⟨i,hi⟩).isLt
    omega
  · omega
  · exact hij

lemma rational_model : ∃t:Fin n → ℚ, (∀i,0 < t i) ∧ StrictMono t ∧
    ∀i j,i < j → (j≤G.h i → t j < t i+1) ∧ (G.h i < j → t i+1 < t j) := by
  obtain ⟨t,ht,he⟩:=ElementaryPositivity.rational_interval_prefix G.extendedH G.extendedH_monotone n
  refine ⟨fun i=>t i.val,fun i=>ht i.val i.isLt,?_,?_⟩
  · intro i j hij
    exact (he i.val j.val hij j.isLt).1
  · intro i j hij
    have H: G.extendedH i.val=(G.h i).val:=by simp [extendedH,i.isLt]
    change (j.val≤(G.h i).val → _) ∧ ((G.h i).val < j.val → _)
    simpa only [H] using (he i.val j.val hij j.isLt).2
end ElementaryPositivity.NaturalUnitIntervalGraph

namespace ElementaryPositivity

lemma phase_rank {n:ℕ} (f:Fin n → ℚ) : ∃r:Equiv.Perm (Fin n),
    ∀i j,r i < r j ↔ f i < f j ∨ (f i=f j ∧ i < j) := by
  let key:PhaseLabel n → Lex (ℚ×Fin n):=fun a=>toLex (f a.val,a.val)
  have hkey:Function.Injective key:=by
    intro a b h
    have hh:=congrArg (fun p:Lex (ℚ×Fin n)=>(ofLex p).2) h
    cases a; cases b; congr 1
  let : LinearOrder (PhaseLabel n):=LinearOrder.lift' key hkey
  let e:Fin n ≃o PhaseLabel n:=Fintype.orderIsoFinOfCardEq (k:=n) (PhaseLabel n) (by
    let e:PhaseLabel n ≃ Fin n:={toFun:=PhaseLabel.val,invFun:=PhaseLabel.mk,left_inv:=fun _=>rfl,right_inv:=fun _=>rfl}
    exact (Fintype.card_congr e).trans (Fintype.card_fin n))
  let r:Equiv.Perm (Fin n):={
    toFun:=fun i=>e.symm ⟨i⟩
    invFun:=fun i=>(e i).val
    left_inv:=fun i=>congrArg PhaseLabel.val (e.apply_symm_apply ⟨i⟩)
    right_inv:=fun i=>e.symm_apply_apply i }
  refine ⟨r,fun i j=>?_⟩
  change e.symm (PhaseLabel.mk i) < e.symm (PhaseLabel.mk j) ↔ _
  rw [e.symm.lt_iff_lt]
  change key (PhaseLabel.mk i) < key (PhaseLabel.mk j) ↔ _
  exact Prod.Lex.lt_iff
end ElementaryPositivity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_GraphTriangularEmbedding
attribute [-instance] _root_.OAI.ElementaryPositivity.TriangularDynamics.instAntisymmCellPhaseLE _root_.OAI.ElementaryPositivity.TriangularDynamics.instDecidableRelCellPhaseLE _root_.OAI.ElementaryPositivity.TriangularDynamics.instIsTransCellPhaseLE _root_.OAI.ElementaryPositivity.TriangularDynamics.instTotalCellPhaseLE
attribute [-simp] _root_.OAI.ElementaryPositivity.NaturalUnitIntervalGraph.edge_comm _root_.OAI.ElementaryPositivity.NaturalUnitIntervalGraph.edge_irrefl _root_.OAI.ElementaryPositivity.NaturalUnitIntervalGraph.mem_edges _root_.OAI.ElementaryPositivity.NaturalUnitIntervalGraph.mem_invertedEdges _root_.OAI.ElementaryPositivity.TriangularDynamics.forwardCoord_roots _root_.OAI.ElementaryPositivity.TriangularDynamics.levelNode_last _root_.OAI.ElementaryPositivity.TriangularDynamics.levelNode_zero _root_.OAI.ElementaryPositivity.TriangularDynamics.mem_phaseCycle _root_.OAI.ElementaryPositivity.TriangularDynamics.omega_anchor_delta _root_.OAI.ElementaryPositivity.TriangularDynamics.omega_anchors _root_.OAI.ElementaryPositivity.TriangularDynamics.omega_delta_anchor _root_.OAI.ElementaryPositivity.TriangularDynamics.omega_delta_delta _root_.OAI.ElementaryPositivity.TriangularDynamics.partialBridge_cycle _root_.OAI.ElementaryPositivity.TriangularDynamics.partialBridge_nil _root_.OAI.ElementaryPositivity.TriangularDynamics.scheduledBridge_self
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

lemma rankedCell_level {n:ℕ} (l:Fin n → ℕ) (r:Equiv.Perm (Fin n)) (i:Fin n) :
    (rankedCell l r i).1.val=n+l i := rfl
lemma rankedCell_row {n:ℕ} (l:Fin n → ℕ) (r:Equiv.Perm (Fin n)) (i:Fin n) :
    cellRow (rankedCell l r i)=(r i).rev.val := rfl
lemma rankedCell_injective {n:ℕ} (l:Fin n → ℕ) (r:Equiv.Perm (Fin n)) :
    Function.Injective (rankedCell l r) := by
  intro i j h
  have H:=congrArg cellRow h
  exact r.injective (Fin.rev_injective (Fin.ext H))
lemma rankedCell_phase {n:ℕ} (l:Fin n → ℕ) (r:Equiv.Perm (Fin n)) (i j:Fin n) :
    phaseEarlier (rankedCell l r i) (rankedCell l r j) ↔ r i < r j := by
  unfold phaseEarlier
  rw [rankedCell_row,rankedCell_row]
  have hrev: (r j).rev.val  <  (r i).rev.val ↔ r i < r j:=Fin.rev_lt_rev
  rw [hrev]
  constructor
  · rintro (h|⟨h,h'⟩)
    · exact h
    · have hij:=r.injective (Fin.rev_injective (Fin.ext h))
      subst j
      exact (lt_irrefl _ h').elim
  · exact Or.inl

lemma floor_pair_comparisons {x y:ℚ} (_hx:0≤x) (hy:0≤y) (hxy:x < y) :
    ⌊x⌋₊≤⌊y⌋₊ ∧
      (⌊x⌋₊=⌊y⌋₊ → x-(⌊x⌋₊:ℚ) < y-(⌊y⌋₊:ℚ)) ∧
      (⌊y⌋₊=⌊x⌋₊+1 → (y < x+1 ↔ y-(⌊y⌋₊:ℚ) < x-(⌊x⌋₊:ℚ))) ∧
      (⌊x⌋₊+2≤⌊y⌋₊ → x+1 < y) := by
  refine ⟨Nat.floor_mono (le_of_lt hxy),?_,?_,?_⟩
  · intro h
    rw [h]
    linarith
  · intro h
    rw [h,Nat.cast_add,Nat.cast_one]
    constructor  <;> intro H  <;> linarith
  · intro h
    have h':(⌊x⌋₊:ℚ)+2≤(⌊y⌋₊:ℚ):=by exact_mod_cast h
    linarith [Nat.lt_floor_add_one x,Nat.floor_le hy]

theorem graph_triangular_embedding {n:ℕ} (G:NaturalUnitIntervalGraph n) :
    ∃d:ℕ,∃b:Fin n ↪ Cell d,∀i j,i < j →
      bridgePositive (b j) (b i)=(if G.Edge i j then 1 else 0) ∧
      bridgePositive (b i) (b j)=0 := by
  obtain ⟨t,ht,hm,he⟩:=G.rational_model
  let l:Fin n → ℕ:=fun i=>⌊t i⌋₊
  let f:Fin n → ℚ:=fun i=>t i-(l i:ℚ)
  obtain ⟨r,hr⟩:=phase_rank f
  refine ⟨n+1+∑j,l j,⟨rankedCell l r,rankedCell_injective l r⟩,?_⟩
  intro i j hij
  have H:=floor_pair_comparisons (le_of_lt (ht i)) (le_of_lt (ht j)) (hm hij)
  change l i≤l j ∧ (l i=l j → f i < f j) ∧
    (l j=l i+1 → (t j < t i+1 ↔ f j < f i)) ∧ (l i+2≤l j → t i+1 < t j) at H
  have hedge:G.Edge i j ↔ j≤G.h i:=by
    simp only [NaturalUnitIntervalGraph.Edge,hij,true_and,not_lt_of_gt hij,false_and,or_false]
  have hclose:G.Edge i j ↔ t j < t i+1:=by
    rw [hedge]
    constructor
    · exact (he i j hij).1
    · intro hh
      by_contra hn
      linarith [(he i j hij).2 (lt_of_not_ge hn)]
  have heq:(rankedCell l r i).1=(rankedCell l r j).1 ↔ l i=l j:=by
    simp only [Fin.ext_iff,rankedCell_level,Nat.add_left_cancel_iff]
  have hnot:(rankedCell l r i).1.val+1≠(rankedCell l r j).1.val ↔ l i+1≠l j:=by
    simp only [rankedCell_level]; omega
  have hji: ¬((rankedCell l r j).1.val+1=(rankedCell l r i).1.val):=by
    simp only [rankedCell_level]
    omega
  by_cases hl:l i=l j
  · have hp:r i < r j:=(hr i j).mpr (Or.inl (H.2.1 hl))
    have htime:t j < t i+1:=by
      have hf0:0≤f i:=sub_nonneg.mpr (Nat.floor_le (le_of_lt (ht i)))
      have hf1:f j < 1:=by dsimp [f,l] <;> linarith [Nat.lt_floor_add_one (t j)]
      dsimp [f] at hf0 hf1
      rw [←hl] at hf1
      linarith
    have hed:=hclose.mpr htime
    constructor
    · simp [bridgePositive,rankedCell_phase,(heq.mpr hl).symm,hp,hed]
    · simp [bridgePositive,rankedCell_phase,heq.mpr hl,not_lt_of_gt hp]
  · have hl':l i < l j:=lt_of_le_of_ne H.1 hl
    have hpnot:¬(rankedCell l r j).1=(rankedCell l r i).1:=by
      intro he'; exact hl (heq.mp he'.symm)
    have hsmall:¬(rankedCell l r i).1=(rankedCell l r j).1:=by
      intro he'; exact hl (heq.mp he')
    constructor
    · rw [bridgePositive,ite_eq_right (by simp [hpnot])]
      have hequiv: (rankedCell l r i).1.val+1=(rankedCell l r j).1.val ∧
          phaseEarlier (rankedCell l r j) (rankedCell l r i) ↔ G.Edge i j:=by
        rw [rankedCell_phase,rankedCell_level,rankedCell_level,hclose]
        constructor
        · rintro ⟨hl1,hp⟩
          have hll:l j=l i+1:=by omega
          rcases (hr j i).mp hp with hf|⟨_,hji'⟩
          · exact (H.2.2.1 hll).mpr hf
          · exact (lt_asymm hij hji').elim
        · intro hh
          have hll:l j=l i+1:=by
            by_contra hn
            have hh':l i+2≤l j:=by omega
            linarith [H.2.2.2 hh']
          refine ⟨by omega,(hr j i).mpr (Or.inl ((H.2.2.1 hll).mp hh))⟩
      change (if (rankedCell l r i).1.val+1=(rankedCell l r j).1.val ∧
        phaseEarlier (rankedCell l r j) (rankedCell l r i) then (1:ℤ) else 0)=_
      simp only [hequiv]
    · simp [bridgePositive,hsmall,hji]
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Histories_GraphCommonHistory
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
variable {n D:ℕ}

lemma squarefree_weight (b:Fin n ↪ Vertex D (Cell D)) :
    vertexWeight (SquarefreeBlocks.target b)=(n:ℤ) := by
  simp only [SquarefreeBlocks.target,map_sum]
  have H:∀i:Fin n,vertexWeight (Pi.single (b i) (1:ℤ))=1:=by
    intro i
    simp [vertexWeight_apply,Pi.single_apply]
  simp only [H,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]

lemma squarefree_rootDegree (b:Fin n ↪ Vertex D (Cell D)) :
    ∃d,HasRootDegree (extendedRoots D) d
      (includeVertices (SquarefreeBlocks.target b)-triangularBase n) := by
  obtain ⟨d,c,hc,he⟩:=triangularVertex_rootDegree (SquarefreeBlocks.target b) (fun a=>by
    rw [SquarefreeBlocks.target_apply]
    split_ifs <;> omega)
  refine ⟨d,c,hc,?_⟩
  change includeVertices (forwardRoots (fun i=>(c i:ℤ)))=_
  change forwardRoots (fun i=>(c i:ℤ))=_ at he
  rw [he,squarefree_weight,map_sub]
  rfl

lemma graphVertex_pair (G:NaturalUnitIntervalGraph n) (b:Fin n ↪ Cell D)
    (hb:∀i j,i < j → bridgePositive (b j) (b i)=(if G.Edge i j then 1 else 0) ∧
      bridgePositive (b i) (b j)=0) (i j:Fin n) (hij:i < j) :
    extendedOmega D (includeVertices (Pi.single (graphVertex b i) 1))
      (includeVertices (Pi.single (graphVertex b j) 1))= -(if G.Edge i j then 1 else 0) := by
  rw [extendedOmega_original]
  change matrixPairing (chartMatrix cellLevel triangularBB)
    (Pi.single (.inr (b i)) 1) (Pi.single (.inr (b j)) 1)=_
  rw [matrixPairing_single]
  change triangularBB (b i) (b j)=_
  rw [triangularBB,(hb i j hij).1,(hb i j hij).2,zero_sub]

theorem graph_common_history_oai (G:NaturalUnitIntervalGraph n) :
    ∃D:ℕ,∃p:LocalHistoryFormula (Extended (Vertex D (Cell D)))
      ((Vertex D (Cell D) → ℝ) × (Vertex D (Cell D) → ℝ)),
      p.Positive (extendedOmega D) (extendedRoots D) extendedCast
        (simpleTotalTransport (extendedOmega D) (extendedRoots D)) ∧
      ∀(r:ℕ) (a:Fin r →₀ ℕ),a.degree=n →
        (∑κ:Fin n → Fin r,
          if G.Proper κ ∧ (∀i,(Finset.univ.filter (fun j=>κ j=i)).card=a i) then
            (↑(LaurentRay.vUnit^(2*(G.coloringInversions κ:ℤ)-(G.edgeCount:ℤ))):LaurentSeries ℚ) else 0)=
        ∑l:{l:p.Leaf // AnchoredLeaf n p l},
          p.leafWeight (extendedOmega D) (extendedRoots D) extendedCast
            (simpleTotalTransport (extendedOmega D) (extendedRoots D)) l.val *
          (∏i:Fin (D+1),MvPolynomial.esymm (Fin r) (LaurentSeries ℚ) (leafProfile n p l i)).coeff a := by
  obtain ⟨D,b,hb⟩:=graph_triangular_embedding G
  obtain ⟨d,hd⟩:=squarefree_rootDegree (graphVertex b)
  obtain ⟨p,hp,hbound,he⟩:=triangular_common_history n d _ hd
  refine ⟨D,p,hp,?_⟩
  intro r a ha
  have hs:(List.ofFn (fun i=>a i)).sum=n:=by
    rw [List.sum_ofFn]
    have H:=Finsupp.sum_fintype a (fun _ k=>k) (fun _=>rfl)
    exact H.symm.trans ha
  let f:ElementaryExpr n:=hs ▸ ElementaryExpr.sequence (List.ofFn (fun i=>a i))
  have hf:triangularExpression f=
      (List.ofFn (fun i=>independentElement LaurentRay.vUnit (extendedOmega D)
        (fun x=>includeVertices (Pi.single x 1)) (a i))).prod := by
    unfold triangularExpression f
    rw [ElementaryExpr.eval_cast,ElementaryExpr.sequence_ofFn_eval]
    rw [show vertexDisplay (includeVertices ∘ anchor) (includeVertices ∘ bridge)=
      (fun x:Vertex D (Cell D)=>includeVertices (Pi.single x 1)) from funext initial_vertexDisplay]
  have hfo:f.ordinary (σ:=Fin (D+1)) (R:=LaurentSeries ℚ)=
      ∏i:Fin r,MvPolynomial.esymm (Fin (D+1)) (LaurentSeries ℚ) (a i):=by
    dsimp [f]
    rw [ElementaryExpr.ordinary_cast,ElementaryExpr.sequence_ofFn_ordinary]
  rw [←G.graph_squarefree_kernel LaurentRay.vUnit (extendedOmega D) extendedOmega_self
    includeVertices includeVertices_injective (graphVertex b) (graphVertex_pair G b hb),←hf,he f]
  apply Finset.sum_congr rfl
  intro l hl
  rw [hfo,ElementaryMatrix.duality]
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

theorem solution : type_of% @OAI.ElementaryPositivity.TriangularDynamics.graph_common_history_oai := @OAI.ElementaryPositivity.TriangularDynamics.graph_common_history_oai
