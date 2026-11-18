-- Prove2me | solution 1 for OAI.ElementaryPositivity.QuantumTorus.literal_isotropic_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T20:00:05.145567+00:00
-- url     : https://prove2.me/submissions/507c2cba-516c-4c0a-a405-f5b9751491f3

import Mathlib
import Definitions.Def_OAIQ368Chrom007
import Definitions.Def_OAIQ368Chrom016
import Definitions.Def_OAIQ368Chrom054
import Theorems.Thm_OAI_ElementaryPositivity_RawShuffle_literalInput_primitiveFactor

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_CovectorFactor
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.PowerSeriesSplit
open PowerSeries
variable {R : Type*} [Ring R]
lemma rightFactor_zero (F : PowerSeries R) (hF : constantCoeff F=1) :
    rightFactor 0 F=F := by
  have H:=uniqueness (0 : R→+R) F 1 F (by simp) hF (by simp)
    (fun n=>by simp) (fun n=>rfl)
  exact H.2.symm
lemma leftFactor_id (F : PowerSeries R) (hF : constantCoeff F=1) :
    leftFactor (AddMonoidHom.id R) F=F := by
  have H:=uniqueness (AddMonoidHom.id R) F F 1 hF (by simp) (by simp)
    (fun n=>rfl) (fun n=>by simp)
  exact H.1.symm
end ElementaryPositivity.PowerSeriesSplit
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesSplit
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M→+M→+ℤ)
lemma positiveProject_zero : positiveProject v Ω (0 : M→+ℝ)=0 := by
  classical
  apply AddMonoidHom.ext
  intro f
  apply Finsupp.ext
  intro m
  change (Finsupp.filter (fun a : M=>0<(0 : ℝ)) f) m=0
  simp
lemma zeroProject_zero : zeroProject v Ω (0 : M→+ℝ)=AddMonoidHom.id _ := by
  classical
  apply AddMonoidHom.ext
  intro f
  apply Finsupp.ext
  intro m
  change (Finsupp.filter (fun a : M=>(0 : ℝ)=0) f) m=f m
  simp
lemma zeroFactor_zero (F : PowerSeries (Torus v Ω)) (hF : constantCoeff F=1) :
    zeroFactor (positiveProject v Ω (0 : M→+ℝ)) (zeroProject v Ω (0 : M→+ℝ)) F=F := by
  rw [positiveProject_zero,zeroProject_zero,zeroFactor,rightFactor_zero _ hF,leftFactor_id _ hF]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_EnergyLaurentSeries
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
attribute [-simp] _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.EnergyLaurent
open scoped LaurentSeries
noncomputable section
variable {A B : Type*}

lemma series_coeff (e : A → ℤ) (h : Admissible e) (j : ℤ) :
    (series e h).coeff j=(Nat.card {a // e a= -j}:ℚ) := by
  classical
  let s : Set A:={a | e a= -j}
  have hs : s.Finite:=Set.finite_coe_iff.mp (h.2 (-j))
  rw [series,HahnSeries.SummableFamily.coeff_hsum_eq_sum_of_subset (t:=hs.toFinset)]
  · have hh : ∀a∈hs.toFinset,(family e h a).coeff j=(1:ℚ) := by
      intro a ha
      have ha' : e a= -j:=hs.mem_toFinset.mp ha
      change (HahnSeries.single (-e a) (1:ℚ)).coeff j=1
      simp [ha']
    rw [Finset.sum_congr rfl hh]
    simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
    rw [←s.ncard_eq_toFinset_card hs]
    rfl
  · intro a ha
    change (HahnSeries.single (-e a) (1:ℚ)).coeff j≠0 at ha
    have hja : e a= -j := by
      simp only [HahnSeries.coeff_single,ne_eq,ite_eq_right_iff,one_ne_zero,imp_false,not_not] at ha
      omega
    exact hs.mem_toFinset.mpr hja

lemma series_eq_of_cards {e : A → ℤ} {f : B → ℤ} (he : Admissible e) (hf : Admissible f)
    (hc : ∀E,Nat.card {a // e a=E}=Nat.card {b // f b=E}) :
    series e he=series f hf := by
  ext j
  rw [series_coeff,series_coeff,hc]

lemma series_mul {e : A → ℤ} {f : B → ℤ} (he : Admissible e) (hf : Admissible f) :
    series e he*series f hf=series (fun p : A×B=>e p.1+f p.2) (admissible_prod he hf) := by
  change (family e he).hsum*(family f hf).hsum=_
  rw [←HahnSeries.SummableFamily.hsum_mul]
  congr 1
  apply HahnSeries.SummableFamily.ext
  intro p
  change HahnSeries.single (-e p.1) (1:ℚ)*HahnSeries.single (-f p.2) 1=
    HahnSeries.single (-(e p.1+f p.2)) 1
  rw [HahnSeries.single_mul_single,mul_one,neg_add]

lemma series_shift {e : A → ℤ} (he : Admissible e) (k : ℤ) :
    series (fun a=>e a+k) (admissible_shift he k)=
      series e he*HahnSeries.single (-k) (1:ℚ) := by
  ext j
  rw [series_coeff,HahnSeries.coeff_mul_single]
  simp only [mul_one]
  rw [series_coeff]
  congr 1
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun a=>by omega)

lemma series_equiv {e : A → ℤ} {f : B → ℤ} (he : Admissible e) (hf : Admissible f)
    (q : A ≃ B) (hq : ∀a,f (q a)=e a) : series e he=series f hf := by
  apply series_eq_of_cards
  intro E
  exact Nat.card_congr (q.subtypeEquiv (fun a=>by rw [hq]))

end
end ElementaryPositivity.EnergyLaurent
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_EnergyLaurentFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.EnergyLaurent
noncomputable section
variable {A : Type*} {e : A → ℤ}

variable {J : Type*} [Fintype J] {B : J → Type*} (f : ∀j,B j → ℤ)

lemma series_sigma (hf : ∀j,Admissible (f j)) :
    series (fun x : Σj,B j=>f x.1 x.2) (admissible_sigma f hf)=∑j,series (f j) (hf j) := by
  classical
  ext j
  simp only [HahnSeries.coeff_sum,series_coeff]
  let : ∀i,Finite {x : B i // f i x= -j} := fun i=>(hf i).2 (-j)
  rw [Nat.card_congr (sigmaEnergyFiber f (-j)),Nat.card_sigma,Nat.cast_sum]

end
end ElementaryPositivity.EnergyLaurent

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_WeightedTorusSeries
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceZeroUnique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.WeightedTorusSeries
open ElementaryPositivity.RawShuffle ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (w : I → ℕ) [hw : Fact (∀i,0<w i)]

lemma sum_split {A : Type*} [AddCommMonoid A] (n : ℕ) (H : (I→ℕ) → (I→ℕ) → A) :
    (∑d : Slice w n,∑s : DimensionSplit d.val,H s.left s.right)=
      ∑k : Fin (n+1),∑d : Slice w k.val,∑e : Slice w (n-k.val),H d.val e.val := by
  classical
  let E := (splitSliceEquiv w n).trans (pairSliceEquiv w n).symm
  calc
    _ = ∑x : (Σ d : Slice w n,DimensionSplit d.val),H x.2.left x.2.right :=
      (Fintype.sum_sigma (fun x : (Σ d : Slice w n,DimensionSplit d.val)=>H x.2.left x.2.right)).symm
    _ = ∑y : (Σ k : Fin (n+1),Slice w k.val × Slice w (n-k.val)),H y.2.1.val y.2.2.val :=
      Fintype.sum_equiv E _ _ (fun _=>rfl)
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro k hk
      exact Fintype.sum_prod_type _

variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (P : (I → ℕ) →+ M)

attribute [local instance] OAI.ElementaryPositivity.WeightedTorusSeries.instRingTorus
attribute [local instance] OAI.ElementaryPositivity.WeightedTorusSeries.instAddCommMonoidTorus
local instance instAddGroupTorus_r284899_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
lemma monomial_sum {A : Type*} (s : Finset A) (m : M) (f : A → R) :
    Torus.monomial v Ω m (∑i∈s,f i)=∑i∈s,Torus.monomial v Ω m (f i) := by
  exact map_sum (Finsupp.singleAddHom m) f s

lemma pushCoeff_convolution (f g : (I→ℕ) → R) (n : ℕ) :
    pushCoeff w v Ω P (convolution v Ω P f g) n=
      ∑k : Fin (n+1),pushCoeff w v Ω P f k.val*pushCoeff w v Ω P g (n-k.val) := by
  classical
  simp only [pushCoeff,convolution,monomial_sum,torus_sum_mul,torus_mul_sum,
    Torus.monomial_mul_monomial]
  have H:=sum_split w n (fun d e=>Torus.monomial v Ω (P d+P e)
    (f d*g e*↑(v^(Ω (P d) (P e)))))
  convert H using 1
  · apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro s hs
    rw [←map_add,DimensionSplit.left_add_right]
  · apply Finset.sum_congr rfl
    intro k hk
    exact Finset.sum_comm

lemma push_convolution (f g : (I→ℕ) → R) :
    push w v Ω P (convolution v Ω P f g)=push w v Ω P f*push w v Ω P g := by
  apply PowerSeries.ext
  intro n
  simp only [push,coeff_mk,coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,←Fin.sum_univ_eq_sum_range]
  exact pushCoeff_convolution w v Ω P f g n

end
end ElementaryPositivity.WeightedTorusSeries

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_InputTorusEnergy
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ)

lemma crossInteraction_offdiagonal (d : I → ℕ) :
    crossInteraction a d=∑ i,∑ j,if i=j then 0 else (a i j:ℤ)*d i*d j := by
  unfold crossInteraction
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro i hi
  have H : (∑ j,(a i j:ℤ)*d i*d j)=
      (a i i:ℤ)*(d i:ℤ)^2+∑ j,if i=j then 0 else (a i j:ℤ)*d i*d j := by
    calc
      _ = ∑ j,((if i=j then (a i i:ℤ)*(d i:ℤ)^2 else 0)+
          if i=j then 0 else (a i j:ℤ)*d i*d j) := by
        apply Finset.sum_congr rfl; intro j hj
        by_cases h : i=j
        · subst j; simp [pow_two,mul_assoc]
        · simp [h]
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  linear_combination H

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma euler_skew_sum (a : I → I → ℕ) (d e : I → ℕ) :
    eulerForm a d e-eulerForm a e d=
      ∑ i,∑ j,((a j i:ℤ)-a i j)*d i*e j := by
  have H₁ : (∑ i,(d i:ℤ)*e i)=(∑ i,(e i:ℤ)*d i) := by
    apply Finset.sum_congr rfl; intro i hi; ring
  have H₂ : (∑ i,∑ j,(a i j:ℤ)*e i*d j)=(∑ i,∑ j,(a j i:ℤ)*d i*e j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i hi
    apply Finset.sum_congr rfl; intro j hj
    ring
  simp only [eulerForm,H₁,H₂,sub_mul,Finset.sum_sub_distrib]
  ring

omit [DecidableEq I] in
lemma euler_skew_plane (a : I → I → ℕ) (c η : I → ℝ) (t : ℝ)
    (ha : ∀ i j,(a j i:ℝ)-a i j=t*(η i*c j-c i*η j)) (d e : I → ℕ) :
    (eulerForm a d e:ℝ)-eulerForm a e d=
      t*(mass η d*mass c e-mass c d*mass η e) := by
  have H:=congrArg (fun k : ℤ=>(k:ℝ)) (euler_skew_sum a d e)
  push_cast at H
  rw [H]
  simp only [ha]
  have HS (f g : I → ℝ) : (∑ i,∑ j,f i*g j)=(∑ i,f i)*(∑ j,g j) := by
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
  calc
    _ = t*((∑ i,∑ j,(d i:ℝ)*η i*((e j:ℝ)*c j))-
        ∑ i,∑ j,(d i:ℝ)*c i*((e j:ℝ)*η j)) := by
      simp only [mul_sub,Finset.mul_sum,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i hi
      apply Finset.sum_congr rfl; intro j hj
      ring
    _ = _ := by rw [HS,HS]; rfl

omit [DecidableEq I] in
theorem slopeEulerSymmetric_of_plane (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (t : ℝ)
    (ha : ∀ i j,(a j i:ℝ)-a i j=t*(η i*c j-c i*η j)) :
    ∀ θ,SlopeEulerSymmetric a c η θ := by
  intro θ d e hd he hs ht
  have H:=euler_skew_plane a c η t ha d e
  rw [mass_eq c η hc d,mass_eq c η hc e,hs,ht] at H
  have Hz : (eulerForm a d e:ℝ)-eulerForm a e d=0 := by
    rw [H]; ring
  exact_mod_cast sub_eq_zero.mp Hz
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_HNSeries
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.WeightedTorusSeries
open ElementaryPositivity.RawShuffle ElementaryPositivity.QuantumTorus PowerSeries
noncomputable section
universe u
variable {I : Type u} [Fintype I]
variable (w : I → ℕ) [hw : Fact (∀i,0<w i)]

variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (P : (I → ℕ) →+ M)

local instance instAddCommMonoidTorus_1_r284899_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
lemma pushCoeff_zero (f : (I→ℕ) → R) :
    pushCoeff w v Ω P f 0=Torus.monomial v Ω 0 (f 0) := by
  classical
  rw [pushCoeff,Fintype.sum_unique]
  change Torus.monomial v Ω (P 0) (f 0)=_
  rw [map_zero]
lemma push_constant (f : (I→ℕ) → R) (hf : f 0=1) : constantCoeff (push w v Ω P f)=1 := by
  rw [push,constantCoeff_mk,pushCoeff_zero,hf]
  rfl

end
end ElementaryPositivity.WeightedTorusSeries

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_SupportedConvolution
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.DimensionSplit.left_swap _root_.OAI.ElementaryPositivity.RawShuffle.DimensionSplit.right_swap _root_.OAI.ElementaryPositivity.RawShuffle.DimensionSplit.swap_swap _root_.OAI.ElementaryPositivity.RawShuffle.cutShapeDimensionEquiv_left _root_.OAI.ElementaryPositivity.RawShuffle.cutShapeDimensionEquiv_right _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.WeightedTorusSeries
open ElementaryPositivity.RawShuffle
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I R M : Type*} [Fintype I] [DecidableEq I] [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (P : (I → ℕ) →+ M)

omit [Fintype I] in
lemma restrictDim_supported (S : Finset I) (d : I → ℕ) : Supported S (restrictDim S d) := by
  intro i hi
  simp [restrictDim,hi]

omit [Fintype I] in
lemma supported_add (S T : Finset I) (d e : I → ℕ) (hd : Supported S d) (he : Supported T e) :
    Supported (S∪T) (d+e) := by
  intro i hi
  have H : i∉S ∧ i∉T := by simpa only [Finset.mem_union,not_or] using hi
  simp [hd i H.1,he i H.2]

omit [Fintype I] in
lemma restrictDim_split (S T : Finset I) (hST : Disjoint S T) (d : I → ℕ)
    (hd : Supported (S∪T) d) : restrictDim S d+restrictDim T d=d := by
  funext i
  by_cases hS : i∈S
  · have hT : i∉T := fun hi=>Finset.disjoint_left.mp hST hS hi
    simp [restrictDim,hS,hT]
  · by_cases hT : i∈T
    · simp [restrictDim,hS,hT]
    · simp [restrictDim,hS,hT,hd i (by simp [hS,hT])]

omit [Fintype I] in
lemma split_left_restrict (S T : Finset I) (hST : Disjoint S T) (d : I → ℕ)
    (s : DimensionSplit d) (hs : Supported S s.left) (ht : Supported T s.right) :
    s.left=restrictDim S d := by
  funext i
  by_cases hS : i∈S
  · have hT : i∉T := fun hi=>Finset.disjoint_left.mp hST hS hi
    have H:=congrFun (DimensionSplit.left_add_right s) i
    simp only [Pi.add_apply,ht i hT,add_zero] at H
    simp [restrictDim,hS,H]
  · simp [restrictDim,hS,hs i hS]

lemma supported_convolution (S T : Finset I) (hST : Disjoint S T)
    (f g : (I → ℕ) → R) (d : I → ℕ) :
    convolution v Ω P (supportedCoefficient S f) (supportedCoefficient T g) d=
      if Supported (S∪T) d then
        f (restrictDim S d)*g (restrictDim T d)*↑(v^(Ω (P (restrictDim S d)) (P (restrictDim T d))))
      else 0 := by
  classical
  unfold convolution
  by_cases hd : Supported (S∪T) d
  · rw [ite_eq_left hd]
    let s₀:=DimensionSplit.ofPair (restrictDim S d) (restrictDim T d) (restrictDim_split S T hST d hd)
    rw [Finset.sum_eq_single s₀]
    · simp [s₀,supportedCoefficient,restrictDim_supported]
    · intro s hs hne
      by_cases hS : Supported S s.left
      · by_cases hT : Supported T s.right
        · exact (hne (DimensionSplit.ext (split_left_restrict S T hST d s hS hT))).elim
        · simp [supportedCoefficient,hT]
      · simp [supportedCoefficient,hS]
    · simp
  · rw [ite_eq_right hd]
    apply Finset.sum_eq_zero
    intro s hs
    by_cases hS : Supported S s.left
    · have hT : ¬Supported T s.right := by
        intro hT
        have H:=supported_add S T s.left s.right hS hT
        rw [DimensionSplit.left_add_right] at H
        exact hd H
      simp [supportedCoefficient,hT]
    · simp [supportedCoefficient,hS]

end
end ElementaryPositivity.WeightedTorusSeries

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_InputOrderedEnergy
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open WeightedTorusSeries
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ)

omit [DecidableEq I] in
lemma crossInteraction_euler (d : I → ℕ) :
    crossInteraction a d=crossDiagonal a d-eulerForm a d d := by
  have H : crossDiagonal a d=(∑ i,(d i:ℤ)*(d i:ℤ))-∑i,(a i i:ℤ)*(d i:ℤ)^2 := by
    rw [crossDiagonal,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [H,crossInteraction,eulerForm]
  ring

omit [DecidableEq I] in
lemma crossDiagonal_add_disjoint (d e : I → ℕ) (hde : ∀i,d i=0 ∨ e i=0) :
    crossDiagonal a (d+e)=crossDiagonal a d+crossDiagonal a e := by
  rw [crossDiagonal,crossDiagonal,crossDiagonal,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rcases hde i with H|H <;> simp [H]

omit [DecidableEq I] in
lemma eulerForm_zero_separated (d e : I → ℕ) (hde : ∀i,d i=0 ∨ e i=0)
    (ha : ∀i j,d i≠0 → e j≠0 → a i j=0) : eulerForm a d e=0 := by
  unfold eulerForm
  have H₁ : (∑i,(d i:ℤ)*(e i:ℤ))=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rcases hde i with H|H <;> simp [H]
  have H₂ : (∑ i,∑j,(a i j:ℤ)*(d i:ℤ)*(e j:ℤ))=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hd : d i=0
    · simp [hd]
    · by_cases he : e j=0
      · simp [he]
      · simp [ha i j hd he]
  rw [H₁,H₂,sub_self]

omit [DecidableEq I] in
lemma crossInteraction_add_separated (d e : I → ℕ) (hde : ∀i,d i=0 ∨ e i=0)
    (ha : ∀i j,d i≠0 → e j≠0 → a i j=0) :
    crossInteraction a (d+e)=crossInteraction a d+crossInteraction a e+
      (eulerForm a d e-eulerForm a e d) := by
  rw [crossInteraction_euler,crossInteraction_euler,crossInteraction_euler,
    crossDiagonal_add_disjoint a d e hde,eulerForm_add_left,eulerForm_add_right,eulerForm_add_right,
    eulerForm_zero_separated a d e hde ha]
  ring

lemma crossInteraction_restrict_union (S T : Finset I) (hST : Disjoint S T)
    (ha : ∀i∈S,∀j∈T,a i j=0) (d : I → ℕ) (hd : Supported (S∪T) d) :
    crossInteraction a d=crossInteraction a (restrictDim S d)+crossInteraction a (restrictDim T d)+
      (eulerForm a (restrictDim S d) (restrictDim T d)-eulerForm a (restrictDim T d) (restrictDim S d)) := by
  conv_lhs => rw [←restrictDim_split S T hST d hd]
  apply crossInteraction_add_separated
  · intro i
    by_cases hS : i∈S
    · exact Or.inr (restrictDim_supported T d i (fun hT=>Finset.disjoint_left.mp hST hS hT))
    · exact Or.inl (restrictDim_supported S d i hS)
  · intro i j hi hj
    apply ha
    · by_contra H
      exact hi (restrictDim_supported S d i H)
    · by_contra H
      exact hj (restrictDim_supported T d j H)

end
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_InputOrderedProduct
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.WeightedTorusSeries
open ElementaryPositivity.RawShuffle QuantumTorus PowerSeries
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I R M : Type*} [Fintype I] [DecidableEq I] [CommRing R] [AddCommGroup M]
variable (a : I → I → ℕ) (u : I → ℕ → R)
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (P : (I → ℕ) →+ M)
variable (hΩ : ∀d e,Ω (P d) (P e)=eulerForm a d e-eulerForm a e d)

include hΩ in
lemma partialCoefficient_union (S T : Finset I) (hST : Disjoint S T)
    (ha : ∀i∈S,∀j∈T,a i j=0) :
    partialCoefficient a u v (S∪T)=convolution v Ω P
      (partialCoefficient a u v S) (partialCoefficient a u v T) := by
  funext d
  rw [partialCoefficient,partialCoefficient,partialCoefficient,supported_convolution v Ω P S T hST]
  unfold supportedCoefficient
  by_cases hd : Supported (S∪T) d
  · rw [ite_eq_left hd,ite_eq_left hd]
    dsimp only
    rw [Finset.prod_union hST,crossInteraction_restrict_union a S T hST ha d hd,←hΩ]
    have hS : (∏i∈S,u i (restrictDim S d i))=∏i∈S,u i (d i) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp only [restrictDim,ite_eq_left hi]
    have hT : (∏i∈T,u i (restrictDim T d i))=∏i∈T,u i (d i) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp only [restrictDim,ite_eq_left hi]
    rw [hS,hT,zpow_add,zpow_add,Units.val_mul,Units.val_mul]
    ring
  · rw [ite_eq_right hd,ite_eq_right hd]

variable (w : I → ℕ) [Fact (∀i,0<w i)]

omit [DecidableEq I] in
lemma partialCoefficient_empty (d : I → ℕ) :
    partialCoefficient a u v ∅ d=if d=0 then 1 else 0 := by
  have H : Supported ∅ d ↔ d=0 := by simp [Supported,funext_iff]
  simp only [partialCoefficient,supportedCoefficient,H,Finset.prod_empty,one_mul]
  split_ifs with hd
  · subst d
    simp [crossInteraction]
  · rfl

local instance partialCoefficientAddCommMonoid_r284899_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
omit [DecidableEq I] in
lemma push_partial_empty : push w v Ω P (partialCoefficient a u v ∅)=1 := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero=>
    rw [coeff_zero_eq_constantCoeff]
    rw [push_constant w v Ω P _ (by simp [partialCoefficient_empty])]
    simp
  | succ n=>
    simp only [push,coeff_mk,pushCoeff,coeff_one,show n+1≠0 from Nat.succ_ne_zero n,ite_false, if_false]
    apply Finset.sum_eq_zero
    intro d hd
    have H : d.val≠0 := by
      intro hzero
      have HH:=d.property
      rw [hzero,map_zero] at HH
      omega
    rw [partialCoefficient_empty,ite_eq_right H,Torus.monomial_zero]

include hΩ in
lemma push_partial_union (S T : Finset I) (hST : Disjoint S T)
    (ha : ∀i∈S,∀j∈T,a i j=0) :
    push w v Ω P (partialCoefficient a u v (S∪T))=
      push w v Ω P (partialCoefficient a u v S)*push w v Ω P (partialCoefficient a u v T) := by
  rw [partialCoefficient_union a u v Ω P hΩ S T hST ha,push_convolution]

include hΩ in

theorem push_partial_list (l : List I) (hl : l.Nodup) (ho : l.Pairwise fun i j=>a i j=0) :
    push w v Ω P (partialCoefficient a u v l.toFinset)=
      (l.map (fun i=>push w v Ω P (partialCoefficient a u v {i}))).prod := by
  induction l with
  | nil=> simpa using push_partial_empty a u v Ω P w
  | cons i l ih=>
    have hnil:=List.nodup_cons.mp hl
    have hord:=List.pairwise_cons.mp ho
    rw [List.toFinset_cons,←Finset.singleton_union]
    rw [push_partial_union a u v Ω P hΩ w {i} l.toFinset]
    · simp only [ih hnil.2 hord.2,List.map_cons,List.prod_cons]
    · simpa using hnil.1
    · intro j hj k hk
      have hji : j=i := by simpa using hj
      subst j
      exact hord.1 k (List.mem_toFinset.mp hk)

end
end ElementaryPositivity.WeightedTorusSeries

end
section
namespace ElementaryPositivity.WeightedTorusSeries
open QuantumTorus PowerSeries
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I R M : Type*} [Fintype I] [DecidableEq I] [CommRing R] [AddCommGroup M]
variable (w : I → ℕ) [hw : Fact (∀i,0<w i)]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (P : (I → ℕ) →+ M)

omit hw in
lemma weight_single (i : I) (k : ℕ) : weight w (Pi.single i k)=k*w i := by
  simp [weight,Pi.single_apply,ite_mul]

omit [Fintype I] in
lemma supported_single_eq (i : I) (d : I → ℕ) (hd : Supported {i} d) : d=Pi.single i (d i) := by
  funext j
  by_cases hj : j=i
  · subst j; simp
  · simp [hj,hd j (by simpa)]

omit [Fintype I] in
lemma single_nsmul (i : I) (k : ℕ) : Pi.single i k=k • (Pi.single i 1 : I → ℕ) := by
  funext j
  by_cases hj : j=i
  · subst j; simp
  · simp [hj]

local instance pushAxisAddCommMonoid_r284899_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
lemma push_axis (i : I) (f : PowerSeries R) :
    push w v Ω P (supportedCoefficient {i} (fun d=>coeff (d i) f))=
      weightedRay v Ω (w i) (P (Pi.single i 1)) f := by
  apply PowerSeries.ext
  intro n
  rw [push,coeff_mk,pushCoeff,coeff_weightedRay]
  by_cases hn : w i∣n
  · rw [ite_eq_left hn]
    let d₀ : Slice w n:=⟨Pi.single i (n/w i),by
      rw [weight_single,Nat.div_mul_cancel hn]⟩
    rw [Finset.sum_eq_single d₀]
    · have HS : Supported {i} d₀.val := by
        intro j hj
        have H : j≠i := by simpa using hj
        simp [d₀,H]
      rw [supportedCoefficient,ite_eq_left HS]
      dsimp only [d₀]
      rw [Pi.single_eq_same,single_nsmul,map_nsmul]
    · intro d hd hne
      have HS : ¬Supported {i} d.val := by
        intro HS
        apply hne
        apply Subtype.ext
        have HE:=d.property
        rw [supported_single_eq i d.val HS,weight_single] at HE
        have HV : d.val i=n/w i := by
          calc
            d.val i=(d.val i*w i)/(w i) := (Nat.mul_div_left _ (hw.out i)).symm
            _=n/(w i) := congrArg (fun x=>x/(w i)) HE
        rw [supported_single_eq i d.val HS,HV]
      rw [supportedCoefficient,ite_eq_right HS,Torus.monomial_zero]
    · simp
  · rw [ite_eq_right hn]
    apply Finset.sum_eq_zero
    intro d hd
    have HS : ¬Supported {i} d.val := by
      intro HS
      apply hn
      have HE:=d.property
      rw [supported_single_eq i d.val HS,weight_single] at HE
      exact ⟨d.val i,by rw [Nat.mul_comm,HE]⟩
    rw [supportedCoefficient,ite_eq_right HS,Torus.monomial_zero]

end
end ElementaryPositivity.WeightedTorusSeries

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_StringStripDimension
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity RawShuffle
noncomputable section
variable {S I : Type*} (a : S → ℕ) (t : S → ℕ) (dim : S → (I → ℕ))

lemma stringStripDimension_energy (k : S → ℤ) (d : I → ℕ) (x : StringCounts a dim d) :
    stringEnergy a dim (fun s=>k s+2*(t s:ℤ)) d x=
      stripEnergy a t dim k (stringStripDimensionEquiv a t dim d x).1.left
        (stringStripDimensionEquiv a t dim d x).2.1+
      stringEnergy a dim k (stringStripDimensionEquiv a t dim d x).1.right
        (stringStripDimensionEquiv a t dim d x).2.2 :=
  stringStrip_energy a t k x.val

end
end ElementaryPositivity.UnitSelections

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_StringStripSeries
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity RawShuffle EnergyLaurent
noncomputable section
variable {S I : Type*} [Fintype I] [DecidableEq I]
variable (a : S → ℕ) (t : S → ℕ) (dim : S → (I → ℕ)) (k : S → ℤ)
variable (τ : (I→ℕ) →+ ℤ) (hτ : ∀s,(t s:ℤ)=τ (dim s))
variable (he : ∀d,Admissible (stringEnergy a dim k d))

include hτ he in
lemma stringStrip_series (d : I → ℕ) :
    series (stringEnergy a dim (fun s=>k s+2*(t s:ℤ)) d)
      (shiftedString_admissible a t dim k τ hτ he d)=
      ∑s : DimensionSplit d,stripSeries a t dim k τ hτ he s.left*
        series (stringEnergy a dim k s.right) (he s.right) := by
  classical
  let f (s : DimensionSplit d) (p : StripCounts a t dim s.left × StringCounts a dim s.right) :=
    stripEnergy a t dim k s.left p.1+stringEnergy a dim k s.right p.2
  have hf : ∀s,Admissible (f s) := fun s=>admissible_prod
    (stripEnergy_admissible a t dim k τ hτ he s.left) (he s.right)
  rw [series_equiv (shiftedString_admissible a t dim k τ hτ he d)
    (admissible_sigma f hf) (stringStripDimensionEquiv a t dim d)
    (fun x=>(stringStripDimension_energy a t dim k d x).symm),series_sigma f hf]
  apply Finset.sum_congr rfl
  intro s hs
  exact (series_mul (stripEnergy_admissible a t dim k τ hτ he s.left) (he s.right)).symm

include hτ he in

theorem stringStrip_scaled (d : I → ℕ) :
    series (stringEnergy a dim k d) (he d)*HahnSeries.single (-(2*τ d)) (1:ℚ)=
      ∑s : DimensionSplit d,stripSeries a t dim k τ hτ he s.left*
        series (stringEnergy a dim k s.right) (he s.right) := by
  rw [←series_shift]
  have H : (fun x : StringCounts a dim d=>stringEnergy a dim k d x+2*τ d)=
      stringEnergy a dim (fun s=>k s+2*(t s:ℤ)) d :=
    funext (fun x=>(stringEnergy_shift a t dim τ hτ k d x).symm)
  simp only [H]
  exact stringStrip_series a t dim k τ hτ he d

end
end ElementaryPositivity.UnitSelections

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_WeightedPushTwist
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.WeightedTorusSeries
open QuantumTorus RawShuffle PowerSeries
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (w : I → ℕ) [Fact (∀i,0<w i)]
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (P : (I→ℕ) →+ M)

attribute [local instance] OAI.ElementaryPositivity.WeightedTorusSeries.instRingTorus_1
local instance instAddCommMonoidTorus_2_r284899_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_1_r284899_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
omit [DecidableEq I] in
lemma push_twist (hΩ : ∀m,Ω m m=0) (m : M) (f : (I→ℕ) → R) :
    push w v Ω P f*C (Torus.X v Ω m)=
      C (Torus.X v Ω m)*push w v Ω P (fun d=>f d*↑(v^(2*Ω (P d) m))) := by
  classical
  apply PowerSeries.ext
  intro n
  rw [coeff_mul_C,coeff_C_mul]
  simp only [push,coeff_mk,pushCoeff]
  rw [torus_sum_mul,torus_mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [Torus.X,Torus.monomial_mul_monomial,mul_one,one_mul]
  rw [add_comm (P d.val) m,alternating_skew Ω hΩ m (P d.val)]
  congr 1
  rw [mul_assoc,←Units.val_mul,←zpow_add]
  congr 2
  ring_nf

lemma convolution_of_isotropic_support (f g : (I→ℕ) → R)
    (h : ∀d e,f d≠0 → g e≠0 → Ω (P d) (P e)=0) (d : I→ℕ) :
    convolution v Ω P f g d=∑s : DimensionSplit d,f s.left*g s.right := by
  classical
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hf : f s.left=0
  · simp only [hf,zero_mul]
  by_cases hg : g s.right=0
  · simp only [hg,mul_zero,zero_mul]
  rw [h _ _ hf hg,zpow_zero,Units.val_one,mul_one]

lemma push_adjoint_of_convolution (hΩ : ∀m,Ω m m=0) (m : M)
    (f q : (I→ℕ) → R) (hf : f 0=1)
    (hq : (fun d=>f d*↑(v^(2*Ω (P d) m)))=convolution v Ω P q f) :
    push w v Ω P f*C (Torus.X v Ω m)*
        PowerSeries.invOfUnit (push w v Ω P f) 1=
      C (Torus.X v Ω m)*push w v Ω P q := by
  rw [push_twist w v Ω P hΩ, hq,push_convolution,mul_assoc]
  have H : push w v Ω P f*PowerSeries.invOfUnit (push w v Ω P f) 1=1 := by
    exact PowerSeries.mul_invOfUnit _ 1 (push_constant w v Ω P f hf)
  rw [mul_assoc,H,mul_one]

end
end ElementaryPositivity.WeightedTorusSeries

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

lemma series {A : Type*} (e : A → ℤ) (he : EnergyLaurent.Admissible e) :
    Positive (EnergyLaurent.series e he) := by
  intro j
  rw [EnergyLaurent.series_coeff]
  exact ⟨_,rfl⟩

end
end ElementaryPositivity.LaurentPositive

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TorusPositive
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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
local instance instAddGroupTorusLaurentSeriesRatVUnit_r284899_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
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

lemma completedPositive_C_X (m : M) : IntegralPositive Ω (C (Torus.X LaurentRay.vUnit Ω m)) := by
  intro n
  rw [coeff_C]
  split
  · exact torusPositive_monomial Ω _ _ positive_one
  · exact torusPositive_zero Ω

lemma IntegralPositive.mul {F G : PowerSeries (Torus LaurentRay.vUnit Ω)}
    (hF : IntegralPositive Ω F) (hG : IntegralPositive Ω G) : IntegralPositive Ω (F*G) := by
  intro n
  rw [coeff_mul]
  exact TorusPositive.sum Ω _ _ (fun p hp=>(hF p.1).mul Ω (hG p.2))

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (w : I → ℕ) [Fact (∀i,0<w i)] (P : (I→ℕ) →+ M)

omit [DecidableEq I] in
lemma push_positive (f : (I→ℕ) → LaurentSeries ℚ) (hf : ∀d,Positive (f d)) :
    IntegralPositive Ω (WeightedTorusSeries.push w LaurentRay.vUnit Ω P f) := by
  intro n
  simp only [WeightedTorusSeries.push,coeff_mk,WeightedTorusSeries.pushCoeff]
  exact TorusPositive.sum Ω _ _ (fun d hd=>torusPositive_monomial Ω _ _ (hf d.val))

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_StringPositiveFactor
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity RawShuffle EnergyLaurent QuantumTorus WallUnits WeightedTorusSeries
open PowerSeries
noncomputable section
variable {S I : Type*} [Fintype I] [DecidableEq I]
variable (a : S → ℕ) (t : S → ℕ) (dim : S → (I→ℕ)) (k : S → ℤ)
variable (he : ∀d,Admissible (stringEnergy a dim k d))
variable (D : AddSubmonoid (I→ℕ)) (hdim : ∀s,dim s∈D)

omit [Fintype I] [DecidableEq I] in
include hdim in
lemma stringSeries_support (d : I→ℕ) (hd : stringSeries a dim k he d≠0) : d∈D := by
  classical
  by_contra H
  let : IsEmpty (StringCounts a dim d) := ⟨fun x=>H (x.property ▸
    countDimension_mem _ _ D (fun s=>hdim s.1) x.val)⟩
  apply hd
  ext j
  rw [stringSeries,series_coeff]
  simp

variable (τ : (I→ℕ) →+ ℤ) (hτ : ∀s,(t s:ℤ)=τ (dim s))
omit [Fintype I] [DecidableEq I] in
include hdim in
lemma stripSeries_support (d : I→ℕ) (hd : stripSeries a t dim k τ hτ he d≠0) : d∈D := by
  classical
  by_contra H
  let : IsEmpty (StripCounts a t dim d) := ⟨fun x=>H (x.property ▸
    countDimension_mem _ _ D (fun s=>hdim s.1) x.val)⟩
  apply hd
  ext j
  rw [stripSeries,series_coeff]
  simp

variable {M : Type*} [AddCommGroup M]
variable (Ω : M →+ M →+ ℤ) (P : (I→ℕ) →+ M)
variable (hiso : ∀d∈D,∀e∈D,Ω (P d) (P e)=0)
variable (m : M) (htwist : ∀d,τ d=Ω (P d) m)

include hiso hdim htwist hτ in
lemma stringSeries_twist_convolution :
    (fun d=>stringSeries a dim k he d*↑(LaurentRay.vUnit^(2*Ω (P d) m)))=
      convolution LaurentRay.vUnit Ω P (stripSeries a t dim k τ hτ he)
        (stringSeries a dim k he) := by
  funext d
  rw [LaurentRay.vUnit_zpow,←htwist]
  rw [convolution_of_isotropic_support LaurentRay.vUnit Ω P _ _
    (fun x y hx hy=>hiso x (stripSeries_support a t dim k he D hdim τ hτ x hx)
      y (stringSeries_support a dim k he D hdim y hy))]
  exact stringStrip_scaled a t dim k τ hτ he d

variable (w : I → ℕ) [Fact (∀i,0<w i)]
include hiso hdim htwist hτ in
lemma stringSeries_adjoint (hΩ : ∀x,Ω x x=0) (hzero : stringSeries a dim k he 0=1) :
    push w LaurentRay.vUnit Ω P (stringSeries a dim k he)*C (Torus.X LaurentRay.vUnit Ω m)*
        invOfUnit (push w LaurentRay.vUnit Ω P (stringSeries a dim k he)) 1=
      C (Torus.X LaurentRay.vUnit Ω m)*push w LaurentRay.vUnit Ω P (stripSeries a t dim k τ hτ he) := by
  exact push_adjoint_of_convolution w LaurentRay.vUnit Ω P hΩ m _ _ hzero
    (stringSeries_twist_convolution a t dim k he D hdim τ hτ Ω P hiso m htwist)

include hiso hdim htwist hτ in

theorem stringSeries_adjoint_positive (hΩ : ∀x,Ω x x=0)
    (hzero : stringSeries a dim k he 0=1) :
    IntegralPositive Ω
      (push w LaurentRay.vUnit Ω P (stringSeries a dim k he)*C (Torus.X LaurentRay.vUnit Ω m)*
        invOfUnit (push w LaurentRay.vUnit Ω P (stringSeries a dim k he)) 1) := by
  rw [stringSeries_adjoint a t dim k he D hdim τ hτ Ω P hiso m htwist w hΩ hzero]
  exact (completedPositive_C_X Ω m).mul Ω (push_positive Ω w P _
    (fun d=>LaurentPositive.series _ (stripEnergy_admissible a t dim k τ hτ he d)))

end
end ElementaryPositivity.UnitSelections

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_StringBackshift
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity RawShuffle EnergyLaurent QuantumTorus WallUnits WeightedTorusSeries
noncomputable section
variable {S I : Type*} [Fintype I] [DecidableEq I]
variable (a : S → ℕ) (t : S → ℕ) (dim : S → (I→ℕ)) (k : S → ℤ)
variable (τ : (I→ℕ) →+ ℤ) (hτ : ∀s,(t s:ℤ)=τ (dim s))
variable (he : ∀d,Admissible (stringEnergy a dim k d))

omit [Fintype I] [DecidableEq I] in
include hτ he in
lemma backshiftString_series (d : I→ℕ) :
    stringSeries a dim (fun s=>k s-2*(t s:ℤ))
      (backshiftString_admissible a t dim k τ hτ he) d=
    stringSeries a dim k he d*HahnSeries.single (2*τ d) (1:ℚ) := by
  rw [stringSeries,stringSeries,←neg_neg (2*τ d),←series_shift]
  apply series_equiv _ _ (Equiv.refl _)
  intro x
  exact (by simpa only [sub_eq_add_neg,id_eq,Equiv.refl_apply] using (stringEnergy_backshift a t dim k τ hτ d x).symm)

include hτ he in
lemma backstripString_series (d : I→ℕ) :
    stringSeries a dim k he d=
      ∑s : DimensionSplit d,
        stripSeries a t dim (fun s=>k s-2*(t s:ℤ)) τ hτ
          (backshiftString_admissible a t dim k τ hτ he) s.left *
        stringSeries a dim (fun s=>k s-2*(t s:ℤ))
          (backshiftString_admissible a t dim k τ hτ he) s.right := by
  have H:=stringStrip_series a t dim (fun s=>k s-2*(t s:ℤ)) τ hτ
    (backshiftString_admissible a t dim k τ hτ he) d
  have hk : (fun s=>k s-2*(t s:ℤ)+2*(t s:ℤ))=k := by funext s; ring
  simpa only [hk,stringSeries] using H
end
end ElementaryPositivity.UnitSelections

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_InputProduct
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.WeightedTorusSeries
open RawShuffle QuantumTorus PowerSeries WallUnits
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I R M : Type*} [Fintype I] [DecidableEq I] [CommRing R] [AddCommGroup M]
variable (a : I → I → ℕ) (u : I → ℕ → R)
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (P : (I → ℕ) →+ M)

lemma crossInteraction_axis (i : I) (d : I → ℕ) (hd : Supported {i} d) : crossInteraction a d=0 := by
  rw [crossInteraction_offdiagonal]
  apply Finset.sum_eq_zero
  intro j hj
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hjk : j=k
  · simp [hjk]
  · rw [ite_eq_right hjk]
    by_cases hji : j=i
    · subst j
      rw [hd k (by simp [Ne.symm hjk]),Nat.cast_zero,mul_zero]
    · rw [hd j (by simp [hji]),Nat.cast_zero,mul_zero,zero_mul]

lemma partialCoefficient_singleton (i : I) :
    partialCoefficient a u v {i}=supportedCoefficient {i} (fun d=>u i (d i)) := by
  funext d
  rw [partialCoefficient,supportedCoefficient,supportedCoefficient]
  by_cases hd : Supported {i} d
  · rw [ite_eq_left hd,ite_eq_left hd]
    simp only [Finset.prod_singleton,crossInteraction_axis a i d hd,zpow_zero,Units.val_one,mul_one]
  · rw [ite_eq_right hd,ite_eq_right hd]

variable (w : I → ℕ) [Fact (∀i,0<w i)]

lemma push_partial_axis_family (i : I) (f : I → PowerSeries R) :
    push w v Ω P (partialCoefficient a (fun j n=>coeff n (f j)) v {i})=
      weightedRay v Ω (w i) (P (Pi.single i 1)) (f i) := by
  rw [partialCoefficient_singleton,push_axis]

end
end ElementaryPositivity.WeightedTorusSeries

namespace ElementaryPositivity.RawShuffle
open QuantumTorus WeightedTorusSeries PowerSeries WallUnits
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I M : Type*} [Fintype I] [DecidableEq I] [AddCommGroup M]
variable (a : I → I → ℕ) (κ : I → ℤ) (ε : I → Bool)
variable (Ω : M →+ M →+ ℤ) (P : (I → ℕ) →+ M)
variable (w : I → ℕ) [Fact (∀i,0<w i)]

omit [DecidableEq I] in
lemma partial_univ_literal :
    partialCoefficient a (fun i n=>coeff n (literalAxisScalar κ ε i)) LaurentRay.vUnit Finset.univ=
      literalInputCoefficient a κ ε := by
  funext d
  have HS : Supported Finset.univ d := by intro i hi; exact (hi (Finset.mem_univ i)).elim
  rw [partialCoefficient,supportedCoefficient,ite_eq_left HS]
  dsimp only [literalAxisScalar]
  simp only [coeff_map,LaurentRay.vUnit_zpow]
  rfl

theorem literalInput_ordered (hΩ : ∀d e,Ω (P d) (P e)=eulerForm a d e-eulerForm a e d)
    (l : List I) (hl : l.Nodup) (hall : l.toFinset=Finset.univ)
    (ho : l.Pairwise fun i j=>a i j=0) :
    push w LaurentRay.vUnit Ω P (literalInputCoefficient a κ ε)=
      (l.map (literalAxis κ ε Ω P w)).prod := by
  have H:=push_partial_list a (fun i n=>coeff n (literalAxisScalar κ ε i))
    LaurentRay.vUnit Ω P hΩ w l hl ho
  rw [hall,partial_univ_literal a κ ε] at H
  rw [H]
  apply congrArg List.prod
  apply List.map_congr_left
  intro i hi
  exact push_partial_axis_family a LaurentRay.vUnit Ω P w i (literalAxisScalar κ ε)

end
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic QuantumTorus
noncomputable section
variable {I M : Type*} [Fintype I] [DecidableEq I] [AddCommGroup M]
variable (Ω : M →+ M →+ ℤ) (p : I → M) (ε : I → Bool)

lemma rootSum_single (i : I) (n : ℕ) : rootSum p (Pi.single i n)=n • p i := by
  classical
  simp [rootSum,Pi.single_apply,ite_smul,Finset.sum_ite_eq']

omit [Fintype I] in
lemma geometricQuiver_diag (i : I) : geometricQuiver Ω p ε i i=elementaryDiagonal ε i := by
  simp [geometricQuiver]

variable (hΩ : ∀m,Ω m m=0)
omit [Fintype I] in
include hΩ in
lemma geometricQuiver_skew (i j : I) :
    (geometricQuiver Ω p ε j i:ℤ)-geometricQuiver Ω p ε i j=Ω (p i) (p j) := by
  by_cases h : i=j
  · subst j; rw [sub_self,hΩ]
  · rw [geometricQuiver,ite_eq_right (Ne.symm h),geometricQuiver,ite_eq_right h,
      alternating_skew Ω hΩ (p j) (p i)]
    omega

include hΩ in
lemma geometricQuiver_euler (d e : I→ℕ) :
    Ω (rootSum p d) (rootSum p e)=
      eulerForm (geometricQuiver Ω p ε) d e-eulerForm (geometricQuiver Ω p ε) e d := by
  rw [euler_skew_sum]
  simp only [rootSum,AddMonoidHom.coe_mk,ZeroHom.coe_mk,map_sum,map_nsmul,
    AddMonoidHom.finsetSum_apply,AddMonoidHom.nsmul_apply,nsmul_eq_mul,
    geometricQuiver_skew Ω p ε hΩ]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

omit [Fintype I] in
include hΩ in
lemma geometricQuiver_forward (i j : I) (hij : i≠j) (hp : 0≤Ω (p i) (p j)) :
    geometricQuiver Ω p ε i j=0 := by
  rw [geometricQuiver,ite_eq_right hij,alternating_skew Ω hΩ (p j) (p i)]
  exact Int.toNat_eq_zero.mpr (by omega)

omit [Fintype I] in
include hΩ in
lemma geometricQuiver_pairwise (l : List I) (hn : l.Nodup)
    (hl : l.Pairwise (fun i j=>0≤Ω (p i) (p j))) :
    l.Pairwise (fun i j=>geometricQuiver Ω p ε i j=0) := by
  apply (hn.and hl).imp
  intro i j h
  exact geometricQuiver_forward Ω p ε hΩ i j h.1 h.2

include hΩ in
lemma geometricQuiver_symmetric (c η : I→ℝ) (hc : ∀i,0 < c i) (t : ℝ)
    (hp : ∀i j,(Ω (p i) (p j):ℝ)=t*(η i*c j-c i*η j)) :
    ∀θ,SlopeEulerSymmetric (geometricQuiver Ω p ε) c η θ := by
  apply slopeEulerSymmetric_of_plane _ c η hc t
  intro i j
  have H:=congrArg (fun z:ℤ=>(z:ℝ)) (geometricQuiver_skew Ω p ε hΩ i j)
  push_cast at H
  exact H.trans (hp i j)

end
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_HNZeroRows
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic SignedMultiplicity UnitSelections EnergyLaurent
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0 < c i)
  [hχ : Fact (∀θ,SlopeEulerSymmetric a c η θ)]

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.instFactSlopeEulerSymmetric
lemma primitiveCountsSeries_zero (θ : ℝ) : primitiveCountsSeries a κ c η hc θ 0=1 := by
  have he : ∀x : PrimitiveCounts a c η hc θ 0,primitiveCountsEnergy a κ c η hc θ 0 x=0 :=
    fun x=>dimensionCounts_zero_energy _ _ (fun x=>x.1.1.property) _ x
  let := dimensionCounts_zero_subsingleton
    (fun x : SlopeStringStart a c η hc θ × ℕ=>slopeStartRowType a c η hc θ x.1≠0)
    (fun x=>x.1.1.val.1.val) (fun x=>x.1.1.property)
  let : Nonempty (PrimitiveCounts a c η hc θ 0) := ⟨⟨zeroCount _,countDimension_zero _ _⟩⟩
  ext j
  rw [primitiveCountsSeries,series_coeff,HahnSeries.coeff_one]
  by_cases hj : j=0
  · subst j
    have H : ∀x : PrimitiveCounts a c η hc θ 0,primitiveCountsEnergy a κ c η hc θ 0 x= -0 := by simpa using he
    simp only [H,neg_zero]
    simp
  · have H : IsEmpty {x : PrimitiveCounts a c η hc θ 0 // primitiveCountsEnergy a κ c η hc θ 0 x= -j} :=
      ⟨fun x=>hj (by have HH:=x.property; rw [he] at HH; omega)⟩
    let := H
    simp [hj]

end
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_PrimitiveRootClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic SignedMultiplicity UnitSelections EnergyLaurent
open QuantumTorus WeightedTorusSeries WallUnits PowerSeries
noncomputable section
variable {I J M : Type*} [Fintype I] [DecidableEq I] [Fintype J] [AddCommGroup M]
variable (a : I→I→ℕ) (κ : I→ℤ) (c η : I→ℝ) (hc : ∀i,0 < c i)
  [hχ : Fact (∀θ,SlopeEulerSymmetric a c η θ)]
local instance instFactSlopeEulerSymmetric_2 (θ : ℝ) : Fact (SlopeEulerSymmetric a c η θ) := ⟨hχ.out θ⟩
end
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GeometricRootClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic QuantumTorus WeightedTorusSeries WallUnits
noncomputable section
variable {I J M : Type*} [Fintype I] [DecidableEq I] [Fintype J] [AddCommGroup M]
variable (p : I→M) (w : I→ℕ) (C : (J→ℤ)→+M)

omit [DecidableEq I] in
lemma rootSum_mem (V : AddSubmonoid M) (hp : ∀i,p i∈V) (d : I→ℕ) : rootSum p d∈V := by
  exact V.sum_mem (fun i _=>V.nsmul_mem (hp i) (d i))

end
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FiniteWallPositive
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic SignedMultiplicity UnitSelections EnergyLaurent
open QuantumTorus WeightedTorusSeries WallUnits PowerSeries
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0 < c i)
  [hχ : Fact (∀θ,SlopeEulerSymmetric a c η θ)]
local instance localInst_r284899_1 (θ : ℝ) : Fact (SlopeEulerSymmetric a c η θ) := ⟨hχ.out θ⟩
variable (w : I → ℕ) [Fact (∀i,0<w i)]
variable {M : Type*} [AddCommGroup M]
variable (Ω : M →+ M →+ ℤ) (P : (I→ℕ) →+ M)
variable (hΩ : ∀x,Ω x x=0)
variable (hgeom : ∀d e,Ω (P d) (P e)=eulerForm a d e-eulerForm a e d)
variable (θ : ℝ) (m : M)
variable (hm : ∀d∈slopeDimensions c η hc θ,0≤Ω (P d) m)

include hΩ hgeom hm in
lemma primitiveFactor_adjoint_positive :
    IntegralPositive Ω
      (push w LaurentRay.vUnit Ω P (primitiveCountsSeries a κ c η hc θ)*
        C (Torus.X LaurentRay.vUnit Ω m)*
        invOfUnit (push w LaurentRay.vUnit Ω P (primitiveCountsSeries a κ c η hc θ)) 1) := by
  let dim : SlopeStringStart a c η hc θ → (I→ℕ) := fun s=>s.1.val.1.val
  let τ : (I→ℕ) →+ ℤ := (Ω.flip m).comp P
  let t : SlopeStringStart a c η hc θ → ℕ := fun s=>(τ (dim s)).toNat
  have hdim : ∀s,dim s∈slopeDimensions c η hc θ := fun s=>s.1.val.1.property
  have ht : ∀s,(t s:ℤ)=τ (dim s) := fun s=>Int.toNat_of_nonneg (hm _ (hdim s))
  have hi : ∀d∈slopeDimensions c η hc θ,∀e∈slopeDimensions c η hc θ,Ω (P d) (P e)=0 := by
    intro d hd e he
    rw [hgeom,eulerForm_slopeDimensions_symm a c η hc θ ⟨d,hd⟩ ⟨e,he⟩,sub_self]
  exact stringSeries_adjoint_positive (slopeStartRowType a c η hc θ) t dim
    (slopeStartParameter a κ c η hc θ) (primitiveCountsEnergy_admissible a κ c η hc θ)
    (slopeDimensions c η hc θ) hdim τ ht Ω P hi m (fun _=>rfl) w hΩ
    (primitiveCountsSeries_zero a κ c η hc θ)

variable (h : M →+ ℝ) (hh : ∀d,h (P d)=slopeValue c η θ d)
include hΩ hgeom hm hh in

theorem finiteInput_zero_adjoint_positive (ε : I → Bool)
    (ha : ∀i,a i i=elementaryDiagonal ε i) :
    let F := PowerSeriesSplit.zeroFactor (positiveProject LaurentRay.vUnit Ω h)
      (zeroProject LaurentRay.vUnit Ω h) (push w LaurentRay.vUnit Ω P (literalInputCoefficient a κ ε))
    IntegralPositive Ω (F*C (Torus.X LaurentRay.vUnit Ω m)*invOfUnit F 1) := by
  dsimp only
  rw [←literalInput_primitiveFactor a κ c η hc w Ω P hgeom h θ hh ε ha]
  exact primitiveFactor_adjoint_positive a κ c η hc w Ω P hΩ hgeom θ m hm

end
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_WeightedInverseAdjoint
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.WeightedTorusSeries
open QuantumTorus RawShuffle PowerSeries
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (P : (I→ℕ) →+ M)

lemma convolution_comm_isotropic (f g : (I→ℕ) → R)
    (h : ∀d e,f d≠0 → g e≠0 → Ω (P d) (P e)=0)
    (h' : ∀d e,g d≠0 → f e≠0 → Ω (P d) (P e)=0) :
    convolution v Ω P f g=convolution v Ω P g f := by
  classical
  funext d
  rw [convolution_of_isotropic_support v Ω P f g h,
    convolution_of_isotropic_support v Ω P g f h']
  let E : DimensionSplit d ≃ DimensionSplit d := {
    toFun:=fun s=>DimensionSplit.ofPair s.right s.left (by rw [add_comm,DimensionSplit.left_add_right])
    invFun:=fun s=>DimensionSplit.ofPair s.right s.left (by rw [add_comm,DimensionSplit.left_add_right])
    left_inv:=by
      intro s
      funext i
      apply Fin.ext
      change d i-(d i-(s i).val)=(s i).val
      have H:=(s i).isLt
      omega
    right_inv:=by
      intro s
      funext i
      apply Fin.ext
      change d i-(d i-(s i).val)=(s i).val
      have H:=(s i).isLt
      omega }
  apply Fintype.sum_equiv E
  intro s
  dsimp only [E,Equiv.coe_fn_mk]
  rw [DimensionSplit.left_ofPair,DimensionSplit.right_ofPair,mul_comm]

variable (w : I → ℕ) [Fact (∀i,0<w i)]
attribute [local instance] OAI.ElementaryPositivity.WeightedTorusSeries.instRingTorus_2
local instance instAddCommMonoidTorus_3_r284899_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_2_r284899_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
lemma push_inverse_adjoint_of_convolution (hΩ : ∀m,Ω m m=0) (m : M)
    (f q : (I→ℕ) → R) (hf : f 0=1)
    (hq : f=convolution v Ω P (fun d=>f d*↑(v^(2*Ω (P d) m))) q) :
    PowerSeries.invOfUnit (push w v Ω P f) 1*C (Torus.X v Ω m)*push w v Ω P f=
      C (Torus.X v Ω m)*push w v Ω P q := by
  let F:=push w v Ω P f
  let X:=C (Torus.X v Ω m)
  let Q:=push w v Ω P q
  have H : F*(X*Q)=X*F := by
    dsimp only [F,X,Q]
    rw [←mul_assoc,push_twist w v Ω P hΩ,mul_assoc,←push_convolution,←hq]
  have Hi : invOfUnit F 1*F=1 :=
    PowerSeries.invOfUnit_mul _ 1 (push_constant w v Ω P f hf)
  change invOfUnit F 1*X*F=X*Q
  calc
    _ = invOfUnit F 1*(X*F) := mul_assoc _ _ _
    _ = invOfUnit F 1*(F*(X*Q)) := by rw [H]
    _ = _ := by rw [←mul_assoc,Hi,one_mul]
end
end ElementaryPositivity.WeightedTorusSeries

end
section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity RawShuffle EnergyLaurent QuantumTorus WallUnits WeightedTorusSeries
open PowerSeries
noncomputable section
variable {S I : Type*} [Fintype I] [DecidableEq I]
variable (a : S → ℕ) (t : S → ℕ) (dim : S → (I→ℕ)) (k : S → ℤ)
variable (he : ∀d,Admissible (stringEnergy a dim k d))
variable (D : AddSubmonoid (I→ℕ)) (hdim : ∀s,dim s∈D)
variable (τ : (I→ℕ) →+ ℤ) (hτ : ∀s,(t s:ℤ)=τ (dim s))
variable {M : Type*} [AddCommGroup M]
variable (Ω : M →+ M →+ ℤ) (P : (I→ℕ) →+ M)
variable (hiso : ∀d∈D,∀e∈D,Ω (P d) (P e)=0)
variable (m : M) (htwist : ∀d,τ d= -Ω (P d) m)

include hdim hτ hiso htwist in
lemma stringSeries_inverse_convolution :
    stringSeries a dim k he=
      convolution LaurentRay.vUnit Ω P
        (fun d=>stringSeries a dim k he d*↑(LaurentRay.vUnit^(2*Ω (P d) m)))
        (stripSeries a t dim (fun s=>k s-2*(t s:ℤ)) τ hτ
          (backshiftString_admissible a t dim k τ hτ he)) := by
  let hg:=backshiftString_admissible a t dim k τ hτ he
  let g:=stringSeries a dim (fun s=>k s-2*(t s:ℤ)) hg
  let q:=stripSeries a t dim (fun s=>k s-2*(t s:ℤ)) τ hτ hg
  have H : (fun d=>stringSeries a dim k he d*↑(LaurentRay.vUnit^(2*Ω (P d) m)))=g := by
    funext d
    rw [LaurentRay.vUnit_zpow]
    dsimp only [g]
    rw [backshiftString_series a t dim k τ hτ he d]
    rw [htwist,mul_neg]
  rw [H]
  change stringSeries a dim k he=convolution LaurentRay.vUnit Ω P g q
  have hgs : ∀d,g d≠0 → d∈D := fun d h=>stringSeries_support a dim _ hg D hdim d h
  have hqs : ∀d,q d≠0 → d∈D := fun d h=>stripSeries_support a t dim _ hg D hdim τ hτ d h
  rw [convolution_comm_isotropic LaurentRay.vUnit Ω P g q
    (fun d e hd he=>hiso d (hgs d hd) e (hqs e he))
    (fun d e hd he=>hiso d (hqs d hd) e (hgs e he))]
  funext d
  rw [convolution_of_isotropic_support LaurentRay.vUnit Ω P q g
    (fun d e hd he=>hiso d (hqs d hd) e (hgs e he))]
  exact backstripString_series a t dim k τ hτ he d

variable (w : I → ℕ) [Fact (∀i,0<w i)]
include hdim hτ hiso htwist in
lemma stringSeries_inverse_adjoint (hΩ : ∀x,Ω x x=0) (hzero : stringSeries a dim k he 0=1) :
    invOfUnit (push w LaurentRay.vUnit Ω P (stringSeries a dim k he)) 1*
        C (Torus.X LaurentRay.vUnit Ω m)*push w LaurentRay.vUnit Ω P (stringSeries a dim k he)=
      C (Torus.X LaurentRay.vUnit Ω m)*push w LaurentRay.vUnit Ω P
        (stripSeries a t dim (fun s=>k s-2*(t s:ℤ)) τ hτ
          (backshiftString_admissible a t dim k τ hτ he)) := by
  exact push_inverse_adjoint_of_convolution LaurentRay.vUnit Ω P w hΩ m _ _ hzero
    (stringSeries_inverse_convolution a t dim k he D hdim τ hτ Ω P hiso m htwist)

include hdim hτ hiso htwist in

theorem stringSeries_inverse_adjoint_positive (hΩ : ∀x,Ω x x=0)
    (hzero : stringSeries a dim k he 0=1) :
    IntegralPositive Ω
      (invOfUnit (push w LaurentRay.vUnit Ω P (stringSeries a dim k he)) 1*
        C (Torus.X LaurentRay.vUnit Ω m)*push w LaurentRay.vUnit Ω P (stringSeries a dim k he)) := by
  rw [stringSeries_inverse_adjoint a t dim k he D hdim τ hτ Ω P hiso m htwist w hΩ hzero]
  exact (completedPositive_C_X Ω m).mul Ω (push_positive Ω w P _
    (fun d=>LaurentPositive.series _ (stripEnergy_admissible a t dim _ τ hτ
      (backshiftString_admissible a t dim k τ hτ he) d)))
end
end ElementaryPositivity.UnitSelections

end
section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic SignedMultiplicity UnitSelections EnergyLaurent
open QuantumTorus WeightedTorusSeries WallUnits PowerSeries
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0 < c i)
  [hχ : Fact (∀θ,SlopeEulerSymmetric a c η θ)]
local instance localInst_r284899_2 (θ : ℝ) : Fact (SlopeEulerSymmetric a c η θ) := ⟨hχ.out θ⟩
variable (w : I → ℕ) [Fact (∀i,0<w i)]
variable {M : Type*} [AddCommGroup M]
variable (Ω : M →+ M →+ ℤ) (P : (I→ℕ) →+ M)
variable (hΩ : ∀x,Ω x x=0)
variable (hgeom : ∀d e,Ω (P d) (P e)=eulerForm a d e-eulerForm a e d)
variable (θ : ℝ) (m : M)
variable (hm : ∀d∈slopeDimensions c η hc θ,Ω (P d) m≤0)

include hΩ hgeom hm in
lemma primitiveFactor_inverse_adjoint_positive :
    IntegralPositive Ω
      (invOfUnit (push w LaurentRay.vUnit Ω P (primitiveCountsSeries a κ c η hc θ)) 1*
        C (Torus.X LaurentRay.vUnit Ω m)*
        push w LaurentRay.vUnit Ω P (primitiveCountsSeries a κ c η hc θ)) := by
  let dim : SlopeStringStart a c η hc θ → (I→ℕ) := fun s=>s.1.val.1.val
  let τ : (I→ℕ) →+ ℤ := -((Ω.flip m).comp P)
  let t : SlopeStringStart a c η hc θ → ℕ := fun s=>(τ (dim s)).toNat
  have hdim : ∀s,dim s∈slopeDimensions c η hc θ := fun s=>s.1.val.1.property
  have ht : ∀s,(t s:ℤ)=τ (dim s) := fun s=>Int.toNat_of_nonneg (neg_nonneg.mpr (hm _ (hdim s)))
  have hi : ∀d∈slopeDimensions c η hc θ,∀e∈slopeDimensions c η hc θ,Ω (P d) (P e)=0 := by
    intro d hd e he
    rw [hgeom,eulerForm_slopeDimensions_symm a c η hc θ ⟨d,hd⟩ ⟨e,he⟩,sub_self]
  exact stringSeries_inverse_adjoint_positive (slopeStartRowType a c η hc θ) t dim
    (slopeStartParameter a κ c η hc θ) (primitiveCountsEnergy_admissible a κ c η hc θ)
    (slopeDimensions c η hc θ) hdim τ ht Ω P hi m (fun _=>rfl) w hΩ
    (primitiveCountsSeries_zero a κ c η hc θ)

variable (h : M →+ ℝ) (hh : ∀d,h (P d)=slopeValue c η θ d)
include hΩ hgeom hm hh in

theorem finiteInput_zero_inverse_adjoint_positive (ε : I → Bool)
    (ha : ∀i,a i i=elementaryDiagonal ε i) :
    let F := PowerSeriesSplit.zeroFactor (positiveProject LaurentRay.vUnit Ω h)
      (zeroProject LaurentRay.vUnit Ω h) (push w LaurentRay.vUnit Ω P (literalInputCoefficient a κ ε))
    IntegralPositive Ω (invOfUnit F 1*C (Torus.X LaurentRay.vUnit Ω m)*F) := by
  dsimp only
  rw [←literalInput_primitiveFactor a κ c η hc w Ω P hgeom h θ hh ε ha]
  exact primitiveFactor_inverse_adjoint_positive a κ c η hc w Ω P hΩ hgeom θ m hm

end
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_GeometricFinitePositive
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic QuantumTorus WeightedTorusSeries WallUnits PowerSeries
noncomputable section
variable {I M : Type*} [Fintype I] [DecidableEq I] [AddCommGroup M]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀p,Ω p p=0)
variable (p : I → M) (κ : I → ℤ) (ε : I → Bool)
variable (w : I → ℕ) [Fact (∀i,0<w i)]
variable (c η : I → ℝ) (hc : ∀i,0 < c i) (t : ℝ)
variable (hp : ∀i j,(Ω (p i) (p j):ℝ)=t*(η i*c j-c i*η j))
variable (l : List I) (hn : l.Nodup) (hall : l.toFinset=Finset.univ)
variable (hl : l.Pairwise (fun i j=>0≤Ω (p i) (p j)))
variable (h : M →+ ℝ) (θ : ℝ) (hh : ∀d,h (rootSum p d)=slopeValue c η θ d)
variable (m : M)

include hΩ hc hp hn hall hl hh in
lemma geometric_zero_adjoint_positive
    (hm : ∀d∈slopeDimensions c η hc θ,0≤Ω (rootSum p d) m) :
    let F := PowerSeriesSplit.zeroFactor (positiveProject LaurentRay.vUnit Ω h)
      (zeroProject LaurentRay.vUnit Ω h)
      ((l.map (literalAxis κ ε Ω (rootSum p) w)).prod)
    IntegralPositive Ω (F*C (Torus.X LaurentRay.vUnit Ω m)*invOfUnit F 1) := by
  let a:=geometricQuiver Ω p ε
  let : Fact (∀θ,SlopeEulerSymmetric a c η θ) :=
    ⟨geometricQuiver_symmetric Ω p ε hΩ c η hc t hp⟩
  have H:=literalInput_ordered a κ ε Ω (rootSum p) w
    (geometricQuiver_euler Ω p ε hΩ) l hn hall
    (geometricQuiver_pairwise Ω p ε hΩ l hn hl)
  dsimp only
  rw [←H]
  exact finiteInput_zero_adjoint_positive a κ c η hc w Ω (rootSum p)
    hΩ (geometricQuiver_euler Ω p ε hΩ) θ m hm h hh ε
    (geometricQuiver_diag Ω p ε)

include hΩ hc hp hn hall hl hh in
lemma geometric_zero_inverse_adjoint_positive
    (hm : ∀d∈slopeDimensions c η hc θ,Ω (rootSum p d) m≤0) :
    let F := PowerSeriesSplit.zeroFactor (positiveProject LaurentRay.vUnit Ω h)
      (zeroProject LaurentRay.vUnit Ω h)
      ((l.map (literalAxis κ ε Ω (rootSum p) w)).prod)
    IntegralPositive Ω (invOfUnit F 1*C (Torus.X LaurentRay.vUnit Ω m)*F) := by
  let a:=geometricQuiver Ω p ε
  let : Fact (∀θ,SlopeEulerSymmetric a c η θ) :=
    ⟨geometricQuiver_symmetric Ω p ε hΩ c η hc t hp⟩
  have H:=literalInput_ordered a κ ε Ω (rootSum p) w
    (geometricQuiver_euler Ω p ε hΩ) l hn hall
    (geometricQuiver_pairwise Ω p ε hΩ l hn hl)
  dsimp only
  rw [←H]
  exact finiteInput_zero_inverse_adjoint_positive a κ c η hc w Ω (rootSum p)
    hΩ (geometricQuiver_euler Ω p ε hΩ) θ m hm h hh ε
    (geometricQuiver_diag Ω p ε)
end
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_OrderedRootReordering
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open RawShuffle SlopeArithmetic WeightedTorusSeries WallUnits UnitSelections PowerSeries
noncomputable section
variable {M J : Type*} [AddCommGroup M] [Fintype J]
variable (Ω : M→+M→+ℤ) (C : (J→ℤ)→+M) (L h : M→+ℝ) (V : AddSubmonoid M)

lemma indexedUnit_bool (a : ℕ) (k : ℤ) :
    indexedUnit (if decide (a=0) then 0 else 1) k=indexedUnit a k := by
  by_cases ha : a=0 <;> simp [indexedUnit,ha]

lemma listLiteral_product (l : List (WallUnitDatum M)) :
    ((List.finRange l.length).map (literalAxis (fun i=> (l.get i).parameter)
      (fun i=>decide ((l.get i).kind=0)) Ω (rootSum (fun i=> (l.get i).root))
      (fun i=> (l.get i).degree))).prod=(l.map (WallUnitDatum.value Ω)).prod := by
  have H : (List.finRange l.length).map (literalAxis (fun i=> (l.get i).parameter)
      (fun i=>decide ((l.get i).kind=0)) Ω (rootSum (fun i=> (l.get i).root))
      (fun i=> (l.get i).degree)) =
      (List.finRange l.length).map (fun i=>(l.get i).value Ω) := by
    apply List.map_congr_left
    intro i hi
    unfold literalAxis literalAxisScalar elementaryDiagonal WallUnitDatum.value
    rw [rootSum_single,one_nsmul,indexedUnit_bool]
  rw [H]
  change ((List.finRange l.length).map (WallUnitDatum.value Ω ∘ l.get)).prod=_
  rw [←List.map_map,List.map_get_finRange]

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_IsotropicLiteralPositive
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open RawShuffle SlopeArithmetic WeightedTorusSeries WallUnits PowerSeries
noncomputable section
variable {M J : Type*} [AddCommGroup M] [Fintype J]
variable (Ω : M→+M→+ℤ) (C : (J→ℤ)→+M) (V : AddSubmonoid M)
variable (hΩ : ∀p,Ω p p=0) (hV : ∀p∈V,∀q∈V,Ω p q=0)
include hΩ hV in
lemma literal_isotropic_adjoint_oai {F : PowerSeries (Torus LaurentRay.vUnit Ω)}
    (hF : F∈literalRootProducts Ω C (fun p=>p∈V)) :
    (∀m,(∀p∈V,0≤Ω p m)→IntegralPositive Ω
      (F*PowerSeries.C (Torus.X LaurentRay.vUnit Ω m)*invOfUnit F 1)) ∧
    (∀m,(∀p∈V,Ω p m≤0)→IntegralPositive Ω
      (invOfUnit F 1*PowerSeries.C (Torus.X LaurentRay.vUnit Ω m)*F)) := by
  classical
  have hconstant:=literalRootProducts_constant Ω C (fun p=>p∈V) hF
  obtain ⟨l,hl,rfl⟩:=hF
  let p : Fin l.length→M:=fun i=>(l.get i).root
  let w : Fin l.length→ℕ:=fun i=>(l.get i).degree
  let c : Fin l.length→ℝ:=fun i=>w i
  let κ : Fin l.length→ℤ:=fun i=>(l.get i).parameter
  let ε : Fin l.length→Bool:=fun i=>decide ((l.get i).kind=0)
  have hall : ∀i,(l.get i).Allowed C (fun p=>p∈V):=fun i=>hl _ (List.get_mem _ _)
  let : Fact (∀i,0<w i):=⟨fun i=>(hall i).1⟩
  have hc : ∀i,0 < c i:=fun i=>by
    change 0<((l.get i).degree:ℝ)
    exact_mod_cast (hall i).1
  have hp : ∀i j,(Ω (p i) (p j):ℝ)=(0:ℝ)*((0:ℝ)*c j-c i*0):=by
    intro i j
    rw [hV _ (hall i).2.2 _ (hall j).2.2]
    simp
  have ho : (List.finRange l.length).Pairwise (fun i j=>0≤Ω (p i) (p j)):=by
    apply List.pairwise_of_forall
    intro i j
    rw [hV _ (hall i).2.2 _ (hall j).2.2]
  have hh : ∀d,(0 : M→+ℝ) (rootSum p d)=slopeValue c (fun _=>0) 0 d:=by
    intro d
    simp [slopeValue,mass]
  have Hprod:=listLiteral_product Ω l
  change ((List.finRange l.length).map (literalAxis κ ε Ω (rootSum p) w)).prod=_ at Hprod
  have Hzero : PowerSeriesSplit.zeroFactor (positiveProject LaurentRay.vUnit Ω (0:M→+ℝ))
      (zeroProject LaurentRay.vUnit Ω (0:M→+ℝ))
      (((List.finRange l.length).map (literalAxis κ ε Ω (rootSum p) w)).prod)=
      (l.map (WallUnitDatum.value Ω)).prod := by
    rw [Hprod,zeroFactor_zero _ _ _ hconstant]
  constructor
  · intro m hm
    have H:=geometric_zero_adjoint_positive Ω hΩ p κ ε w c (fun _=>0) hc 0 hp
      (List.finRange l.length) (List.nodup_finRange _) (List.toFinset_finRange _) ho
      (0:M→+ℝ) 0 hh m (fun d hd=>hm _ (rootSum_mem p V (fun i=>(hall i).2.2) d))
    dsimp only at H
    rwa [Hzero] at H
  · intro m hm
    have H:=geometric_zero_inverse_adjoint_positive Ω hΩ p κ ε w c (fun _=>0) hc 0 hp
      (List.finRange l.length) (List.nodup_finRange _) (List.toFinset_finRange _) ho
      (0:M→+ℝ) 0 hh m (fun d hd=>hm _ (rootSum_mem p V (fun i=>(hall i).2.2) d))
    dsimp only at H
    rwa [Hzero] at H
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.ElementaryPositivity.QuantumTorus.literal_isotropic_adjoint_oai.{u_1, u_2} := @OAI.ElementaryPositivity.QuantumTorus.literal_isotropic_adjoint_oai.{u_1, u_2}
