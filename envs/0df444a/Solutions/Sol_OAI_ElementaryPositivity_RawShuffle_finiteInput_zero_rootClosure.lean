-- Prove2me | solution 1 for OAI.ElementaryPositivity.RawShuffle.finiteInput_zero_rootClosure
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T20:08:59.310198+00:00
-- url     : https://prove2.me/submissions/1da8b037-239e-43df-bd33-91f8cb059ac7

import Mathlib
import Definitions.Def_OAIQ368Chrom007
import Definitions.Def_OAIQ368Chrom013
import Definitions.Def_OAIQ368Chrom055
import Theorems.Thm_OAI_ElementaryPositivity_RawShuffle_literalInput_primitiveFactor

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_EnergyLaurentSeries
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
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

lemma series_sum {e : A → ℤ} {f : B → ℤ} (he : Admissible e) (hf : Admissible f) :
    series (Sum.elim e f) (admissible_sum he hf)=series e he+series f hf := by
  ext j
  rw [HahnSeries.coeff_add,series_coeff,series_coeff,series_coeff]
  let : Finite {a // e a= -j}:=he.2 (-j)
  let : Finite {b // f b= -j}:=hf.2 (-j)
  let q : {x // Sum.elim e f x= -j} ≃ ({a // e a= -j} ⊕ {b // f b= -j}) := Equiv.subtypeSum
  rw [Nat.card_congr q,Nat.card_sum,Nat.cast_add]

end
end ElementaryPositivity.EnergyLaurent
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_WallUnits
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.WallUnits
open PowerSeries

section Field
variable {K : Type*} [Field K]

theorem rescale_inv_of_const_one (a : K) (F : PowerSeries K)
    (hF : PowerSeries.constantCoeff F = 1) :
    PowerSeries.rescale a F⁻¹ = (PowerSeries.rescale a F)⁻¹ := by
  have hR : PowerSeries.constantCoeff (PowerSeries.rescale a F) ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_rescale,
      pow_zero, one_mul, PowerSeries.coeff_zero_eq_constantCoeff, hF]
    exact one_ne_zero
  apply (PowerSeries.eq_inv_iff_mul_eq_one hR).2
  rw [← map_mul, PowerSeries.inv_mul_cancel F (by simp [hF]), map_one]

end Field

end ElementaryPositivity.WallUnits
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RayLaurentExpansion
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder _root_.OAI.ElementaryPositivity.RawShuffle.globalStringIndexLinearOrder _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.WallUnits
open PowerSeries
open scoped LaurentSeries RatFunc
noncomputable section
namespace LaurentRay
lemma map_complete {K L : Type*} [Field K] [Field L] (φ : K →+* L) (q u : K) :
    PowerSeries.map φ (complete q u)=complete (φ q) (φ u) := by
  unfold complete
  have hm : PowerSeries.map φ (elementary q (-u))=elementary (φ q) (-φ u) := by
    rw [map_elementary,map_neg]
  apply (PowerSeries.eq_inv_iff_mul_eq_one (by rw [constant_elementary]; exact one_ne_zero)).mpr
  rw [←hm,←map_mul,PowerSeries.inv_mul_cancel _ (by rw [constant_elementary]; exact one_ne_zero),map_one]

lemma complete_atInfinity (k : ℤ) :
    PowerSeries.map atInfinity (complete RationalRay.q (RationalRay.v^k))=
      complete (HahnSeries.single (2:ℤ) (1:ℚ)) (HahnSeries.single (-k) (1:ℚ)) := by
  rw [map_complete,atInfinity_q,atInfinity_v_pow]

end LaurentRay
end
end ElementaryPositivity.WallUnits
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_UnitIndexEnergy
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.UnitSelections
noncomputable section

lemma twice_staircase (n : ℕ) : 2*(∑i : Fin n,(i.val:ℤ))=(n:ℤ)*((n:ℤ)-1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last,Nat.cast_add,Nat.cast_one]
    nlinarith

lemma staircase_weight (n : ℕ) (f : Weak n) :
    2*weight (staircaseEquiv n f).val=2*weight f.val+(n:ℤ)*((n:ℤ)-1) := by
  change 2*(∑i : Fin n,((f.val i+i.val:ℕ):ℤ))=_
  simp only [Nat.cast_add,Finset.sum_add_distrib,mul_add,twice_staircase,weight]

end
end ElementaryPositivity.UnitSelections
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_WeakUnitRecursion
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.UnitSelections
noncomputable section

lemma weight_prependZero (n : ℕ) (f : Weak n) : weight (prependZero n f).val=weight f.val := by
  rw [weight,Fin.sum_univ_succ]
  simp only [prependZero,Fin.cons_zero,Fin.cons_succ,Nat.cast_zero,zero_add]
  rfl

lemma weight_shiftOne (n : ℕ) (f : Weak n) : weight (shiftOne n f).val=weight f.val+n := by
  simp [weight,shiftOne,Finset.sum_add_distrib]

lemma weakSplit_inv_energy (n : ℕ) (k : ℤ) (p : Weak n ⊕ Weak (n+1)) :
    ((n+1:ℕ):ℤ)*k-2*weight (weakSplit n |>.symm p).val=
      Sum.elim (fun f : Weak n=>(n:ℤ)*k-2*weight f.val+k)
        (fun f : Weak (n+1)=>((n+1:ℕ):ℤ)*k-2*weight f.val-2*(n+1)) p := by
  cases p with
  | inl f =>
    change ((n+1:ℕ):ℤ)*k-2*weight (prependZero n f).val=_
    rw [weight_prependZero]
    simp only [Sum.elim_inl,Nat.cast_add,Nat.cast_one]
    ring
  | inr f =>
    change ((n+1:ℕ):ℤ)*k-2*weight (shiftOne (n+1) f).val=_
    rw [weight_shiftOne]
    simp only [Sum.elim_inr,Nat.cast_add,Nat.cast_one]
    ring
end
end ElementaryPositivity.UnitSelections
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_UnitSelectionLaurent
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceZeroUnique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.UnitSelections
open EnergyLaurent
open scoped LaurentSeries
noncomputable section

lemma weakSeries_zero (k : ℤ) : weakSeries 0 k=1 := by
  let f : Weak 0:=⟨fun i=>Fin.elim0 i,by intro i; exact Fin.elim0 i⟩
  let : Unique (Weak 0):=⟨⟨f⟩,fun g=>Subsingleton.elim _ _⟩
  change (family (weakEnergy 0 k) (weakAdmissible 0 k)).hsum=1
  rw [HahnSeries.SummableFamily.hsum_unique]
  change HahnSeries.single (-(weakEnergy 0 k f)) (1:ℚ)=1
  simp only [weakEnergy,weight,Finset.univ_eq_empty,Finset.sum_empty,Int.natCast_zero,
    zero_mul,mul_zero,sub_self,neg_zero,HahnSeries.single_zero_one]

lemma weakSeries_recursion (n : ℕ) (k : ℤ) :
    weakSeries (n+1) k=weakSeries n k*HahnSeries.single (-k) (1:ℚ)+
      weakSeries (n+1) k*HahnSeries.single (2*(n+1:ℤ)) (1:ℚ) := by
  let he:=admissible_shift (weakAdmissible n k) k
  let hf:=admissible_shift (weakAdmissible (n+1) k) (-2*(n+1:ℤ))
  have hh:=series_equiv (admissible_sum he hf) (weakAdmissible (n+1) k)
    (weakSplit n).symm (fun p=>by
      simpa only [weakEnergy,sub_eq_add_neg,neg_mul] using weakSplit_inv_energy n k p)
  rw [series_sum he hf,series_shift (weakAdmissible n k),series_shift (weakAdmissible (n+1) k)] at hh
  simpa only [weakSeries,neg_mul,neg_neg] using hh.symm

lemma weakSeries_recursion_q (n : ℕ) (k : ℤ) :
    weakSeries (n+1) k*(1-(HahnSeries.single 2 (1:ℚ))^(n+1))=
      HahnSeries.single (-k) (1:ℚ)*weakSeries n k := by
  have hh:=weakSeries_recursion n k
  rw [HahnSeries.single_pow,one_pow]
  have hn : (n+1) • (2:ℤ)=2*(n+1:ℤ) := by simp only [nsmul_eq_mul,Nat.cast_add,Nat.cast_one] <;> ring
  rw [hn]
  linear_combination hh
end
end ElementaryPositivity.UnitSelections
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_CompleteUnitRecursion
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.WallUnits
open PowerSeries
variable {K : Type*} [Field K]
lemma complete_tail (q u : K) (hq : ∀ n : ℕ,1-q^(n+1)≠0) :
    PowerSeries.rescale q (complete q u)=(1+PowerSeries.C (-u)*PowerSeries.X)*complete q u := by
  rw [complete,rescale_inv_of_const_one _ _ (constant_elementary _ _)]
  symm
  apply (PowerSeries.eq_inv_iff_mul_eq_one (by
    rw [←PowerSeries.coeff_zero_eq_constantCoeff,coeff_rescale,pow_zero,one_mul,
      PowerSeries.coeff_zero_eq_constantCoeff,constant_elementary]
    exact one_ne_zero)).mpr
  calc
    ((1+C (-u)*X)*(elementary q (-u))⁻¹)*PowerSeries.rescale q (elementary q (-u))=
        (elementary q (-u))⁻¹*((1+C (-u)*X)*PowerSeries.rescale q (elementary q (-u))) := by ring
    _=(elementary q (-u))⁻¹*elementary q (-u) := by rw [←elementary_tail q (-u) hq]
    _=1 := PowerSeries.inv_mul_cancel _ (by rw [constant_elementary]; exact one_ne_zero)

lemma complete_coeff_recursion (q u : K) (hq : ∀ n : ℕ,1-q^(n+1)≠0) (n : ℕ) :
    coeff (n+1) (complete q u)*(1-q^(n+1))=u*coeff n (complete q u) := by
  have h:=congrArg (coeff (n+1)) (complete_tail q u hq)
  rw [add_mul,one_mul,map_add,mul_assoc,coeff_C_mul,coeff_succ_X_mul,coeff_rescale] at h
  linear_combination -h

lemma complete_coeff_zero (q u : K) : coeff 0 (complete q u)=1 := by
  rw [complete,coeff_zero_eq_constantCoeff,PowerSeries.constantCoeff_inv,constant_elementary,inv_one]
end ElementaryPositivity.WallUnits
namespace ElementaryPositivity.WallUnits
open PowerSeries
variable {K : Type*} [Field K]
lemma elementaryCoeff_eq_complete (q u : K) (hq : ∀ n : ℕ,1-q^(n+1)≠0) (n : ℕ) :
    elementaryCoeff q u n=q^(∑i∈Finset.range n,i)*coeff n (complete q u) := by
  induction n with
  | zero => simp [elementaryCoeff,complete_coeff_zero]
  | succ n ih =>
    have hh : coeff (n+1) (complete q u)=u*coeff n (complete q u)/(1-q^(n+1)) :=
      (eq_div_iff (hq n)).mpr (complete_coeff_recursion q u hq n)
    rw [elementaryCoeff,ih,Finset.sum_range_succ,pow_add,hh]
    ring
end ElementaryPositivity.WallUnits
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_CompleteUnit
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq _root_.OAI.ElementaryPositivity.RawShuffle.globalStringIndexLinearOrder _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.UnitSelections
open EnergyLaurent WallUnits PowerSeries
open scoped LaurentSeries
noncomputable section

theorem weakSeries_eq_complete (n : ℕ) (k : ℤ) :
    weakSeries n k=coeff n (complete (HahnSeries.single 2 (1:ℚ)) (HahnSeries.single (-k) 1)) := by
  induction n with
  | zero => rw [weakSeries_zero,complete_coeff_zero]
  | succ n ih =>
    apply mul_right_cancel₀ (laurent_q_not_root n)
    rw [weakSeries_recursion_q,complete_coeff_recursion _ _ laurent_q_not_root,ih]

theorem complete_literal_expansion (n : ℕ) (k : ℤ) :
    LaurentRay.atInfinity (coeff n (complete RationalRay.q (RationalRay.v^k)))=weakSeries n k := by
  rw [weakSeries_eq_complete,←LaurentRay.complete_atInfinity,coeff_map]
end
end ElementaryPositivity.UnitSelections
end
section
namespace ElementaryPositivity.UnitSelections
open EnergyLaurent WallUnits PowerSeries
open scoped LaurentSeries
noncomputable section

lemma strictSeries_staircase (n : ℕ) (k : ℤ) :
    strictSeries n k=weakSeries n k*HahnSeries.single ((n:ℤ)*((n:ℤ)-1)) (1:ℚ) := by
  have hh := series_equiv (admissible_shift (weakAdmissible n k) (-((n:ℤ)*((n:ℤ)-1))))
    (strictAdmissible n k) (staircaseEquiv n) (fun f=>by
      have hf:=staircase_weight n f
      unfold strictEnergy weakEnergy
      omega)
  rw [series_shift (weakAdmissible n k)] at hh
  simpa only [neg_neg,weakSeries,strictSeries] using hh.symm

lemma twice_range_staircase (n : ℕ) :
    2*((∑i∈Finset.range n,i:ℕ):ℤ)=(n:ℤ)*((n:ℤ)-1) := by
  have hh:=twice_staircase n
  rw [Fin.sum_univ_eq_sum_range] at hh
  simpa only [Nat.cast_sum] using hh

theorem elementary_literal_expansion (n : ℕ) (k : ℤ) :
    LaurentRay.atInfinity (coeff n (elementary RationalRay.q (RationalRay.v^k)))=strictSeries n k := by
  rw [coeff_elementary,elementaryCoeff_eq_complete _ _ RationalRay.q_not_root_unity,
    map_mul,map_pow,LaurentRay.atInfinity_q,complete_literal_expansion,strictSeries_staircase,
    HahnSeries.single_pow,one_pow]
  have he : (∑i∈Finset.range n,i) • (2:ℤ)=(n:ℤ)*((n:ℤ)-1) := by
    rw [nsmul_eq_mul,mul_comm]
    exact twice_range_staircase n
  rw [he,mul_comm]
end
end ElementaryPositivity.UnitSelections
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
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_CountSumDimension
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.SignedMultiplicity
open RawShuffle EnergyLaurent
noncomputable section
variable {A B I : Type*} [Fintype I] [DecidableEq I]
variable (ea : A → Prop) (eb : B → Prop) (da : A → (I→ℕ)) (db : B → (I→ℕ))
variable (ka : A → ℤ) (kb : B → ℤ)

variable (ha : ∀d,Admissible (fun f : DimensionCounts ea da d=>countEnergy ea ka f.val))
variable (hb : ∀d,Admissible (fun f : DimensionCounts eb db d=>countEnergy eb kb f.val))

lemma countSum_series (d : I→ℕ) :
    series _ (countSum_admissible ea eb da db ka kb ha hb d)=
      ∑s : DimensionSplit d,series _ (ha s.left)*series _ (hb s.right) := by
  let k (s : DimensionSplit d) (f : DimensionCounts ea da s.left × DimensionCounts eb db s.right) :=
    countEnergy ea ka f.1.val+countEnergy eb kb f.2.val
  rw [series_equiv _ (admissible_sigma k (fun s=>admissible_prod (ha s.left) (hb s.right)))
    (countSumDimensionEquiv ea eb da db d) (fun f=>(countSumDimension_energy ea eb da db ka kb d f).symm),
    series_sigma]
  apply Finset.sum_congr rfl
  intro s hs
  exact (series_mul (ha s.left) (hb s.right)).symm
end
end ElementaryPositivity.SignedMultiplicity

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
local instance instAddGroupTorus_r82e08d_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_IndexedUnit
attribute [-instance] _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.UnitSelections
open EnergyLaurent WallUnits PowerSeries
open scoped LaurentSeries
noncomputable section

theorem indexedUnit_literal_expansion (a n : ℕ) (k : ℤ) :
    LaurentRay.atInfinity (coeff n (indexedUnit a k))=indexedUnitSeries a n k := by
  unfold indexedUnit
  by_cases h : a=0
  · rw [ite_eq_left h,elementary_literal_expansion]
    exact series_equiv (strictAdmissible n k) (unitAdmissible a n k)
      (strictUnitEquiv a n h) (fun _=>rfl)
  · rw [ite_eq_right h,complete_literal_expansion]
    exact series_equiv (weakAdmissible n k) (unitAdmissible a n k)
      (weakUnitEquivSame a n h) (fun _=>rfl)

end
end ElementaryPositivity.UnitSelections
end
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

local instance instAddCommMonoidTorus_1_r82e08d_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
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
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_WeightedPushTwist
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
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

end
end ElementaryPositivity.WeightedTorusSeries

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_LaurentContinuity
attribute [-simp] _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LaurentPrecision
open Filter
open scoped LaurentSeries

lemma agrees_refl (b : ℤ) (f : Series) : Agrees b f f := fun _ _=>rfl
lemma agrees_add {b : ℤ} {f f' g g' : Series} (hf : Agrees b f f') (hg : Agrees b g g') :
    Agrees b (f+g) (f'+g') := by
  intro j hj
  simp only [HahnSeries.coeff_add,hf j hj,hg j hj]

variable {ι : Type*} (l : Filter ι)

lemma converges_const (F : Series) : Converges l (fun _=>F) F :=
  fun N=>Eventually.of_forall (fun _=>agrees_refl N F)

lemma Converges.add {f g : ι → Series} {F G : Series}
    (hf : Converges l f F) (hg : Converges l g G) :
    Converges l (fun i=>f i+g i) (F+G) := by
  intro N
  filter_upwards [hf N,hg N] with i hi hj
  exact agrees_add hi hj

lemma Converges.sum {α : Type*} (s : Finset α) {f : α → ι → Series} {F : α → Series}
    (h : ∀a∈s,Converges l (f a) (F a)) :
    Converges l (fun i=>∑a∈s,f a i) (∑a∈s,F a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using converges_const l 0
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using
      (h a (Finset.mem_insert_self _ _)).add l (ih (fun b hb=>h b (Finset.mem_insert_of_mem hb)))

end ElementaryPositivity.LaurentPrecision

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_WeightedRay
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceZeroUnique
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.WeightedTorusSeries
open QuantumTorus PowerSeries
noncomputable section
variable {I : Type*} [Fintype I]
variable (w : I→ℕ) [Fact (∀i,0<w i)]

lemma weight_pos (δ : I→ℕ) (hδ : δ≠0) : 0<weight w δ := by
  obtain ⟨i,hi⟩:=Function.ne_iff.mp hδ
  exact lt_of_lt_of_le (Nat.pos_of_ne_zero hi) (coord_le_weight w δ i)

variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M→+M→+ℤ) (P : (I→ℕ)→+M)

local instance pushRayAddGroup_r82e08d_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
lemma push_on_ray (δ : I→ℕ) (f : (I→ℕ)→R) (F : PowerSeries R)
    (hon : ∀n:ℕ,f (n • δ)=coeff n F)
    (hoff : ∀d,(∀n:ℕ,n • δ≠d) → f d=0) :
    push w v Ω P f=weightedRay v Ω (weight w δ) (P δ) F := by
  classical
  apply PowerSeries.ext
  intro n
  rw [push,coeff_mk,coeff_weightedRay]
  change (∑d : Slice w n,Torus.monomial v Ω (P d.val) (f d.val))=_
  split_ifs with hd
  · let d : Slice w n:=⟨(n/weight w δ) • δ,by
      rw [map_nsmul]
      exact Nat.div_mul_cancel hd⟩
    rw [Finset.sum_eq_single d]
    · change Torus.monomial v Ω (P ((n/weight w δ) • δ)) (f ((n/weight w δ) • δ))=_
      rw [hon,map_nsmul]
    · intro e he hne
      rw [hoff]
      · simp [Torus.monomial]
      intro m hm
      have hh:=congrArg (weight w) hm
      rw [map_nsmul,e.property] at hh
      have hw : weight w δ≠0 := by
        intro hz
        have hn : n=0 := by simpa only [hz,smul_zero] using hh.symm
        subst n
        have hδ : δ=0 := by
          funext i
          exact Nat.eq_zero_of_le_zero (by simpa only [hz] using coord_le_weight w δ i)
        apply hne
        apply Subtype.ext
        simpa only [d,hδ,smul_zero] using hm.symm
      have hm' : m=n/weight w δ := by
        change m*weight w δ=n at hh
        rw [←hh,Nat.mul_div_left _ (Nat.pos_of_ne_zero hw)]
      apply hne
      exact Subtype.ext (by simpa only [d,hm'] using hm.symm)
    · simp
  · apply Finset.sum_eq_zero
    intro d hd'
    rw [hoff]
    · simp [Torus.monomial]
    intro m hm
    apply hd
    have hh:=congrArg (weight w) hm
    rw [map_nsmul,d.property] at hh
    exact ⟨m,by simpa [nsmul_eq_mul,mul_comm] using hh.symm⟩
end
end ElementaryPositivity.WeightedTorusSeries

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_StringPositiveFactor
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

end
end ElementaryPositivity.UnitSelections

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_EnergyLimit
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.EnergyLaurent
open LaurentPrecision
noncomputable section
variable {A T : Type*} (e : A → ℤ) (he : Admissible e)

variable (s : A → Finset T)

lemma support_le_cutoff [DecidableEq T] (L : ℤ) (a : A) (ha : L≤e a) :
    s a⊆finiteSupportCutoff e he s L := by
  intro t ht
  exact Finset.mem_biUnion.mpr ⟨a,(finite_above e he L).mem_toFinset.mpr ha,ht⟩

lemma supportRestricted_coeff (S : Finset T) (j : ℤ)
    (hs : ∀a,e a= -j → s a⊆S) :
    (supportRestrictedSeries e he s S).coeff j=(series e he).coeff j := by
  rw [supportRestrictedSeries,series_coeff,series_coeff]
  congr 1
  apply Nat.card_congr
  exact {
    toFun:=fun a=>⟨a.val.val,a.property⟩
    invFun:=fun a=>⟨⟨a.val,hs a.val a.property⟩,a.property⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl }

lemma supportRestricted_agrees [DecidableEq T] (S : Finset T) (N : ℤ)
    (hs : finiteSupportCutoff e he s (1-N)⊆S) :
    Agrees N (supportRestrictedSeries e he s S) (series e he) := by
  intro j hj
  apply supportRestricted_coeff
  intro a ha
  exact (support_le_cutoff e he s (1-N) a (by omega)).trans hs

theorem finiteSupport_converges :
    Converges (Filter.atTop : Filter (Finset T)) (supportRestrictedSeries e he s) (series e he) := by
  classical
  intro N
  filter_upwards [Filter.eventually_ge_atTop (finiteSupportCutoff e he s (1-N))] with S hS
  exact supportRestricted_agrees e he s S N hS

end
end ElementaryPositivity.EnergyLaurent

end
section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity EnergyLaurent LaurentPrecision
noncomputable section
attribute [local instance] Classical.propDecidable
variable {S I : Type*} (a : S → ℕ) (dim : S → (I→ℕ)) (k : S → ℤ)
variable (he : ∀d,Admissible (stringEnergy a dim k d))

lemma finiteStartSeries_eq (T : Finset S) (d : I→ℕ) :
    finiteStartSeries a dim k he T d=
      supportRestrictedSeries (stringEnergy a dim k d) (he d) (startSupport a dim d) T := by
  exact series_equiv _ _ (finiteStartEquiv a dim T d) (finiteStart_energy a dim k T d)

theorem finiteStartSeries_converges (d : I→ℕ) :
    Converges (Filter.atTop : Filter (Finset S)) (fun T=>finiteStartSeries a dim k he T d)
      (stringSeries a dim k he d) := by
  simp_rw [finiteStartSeries_eq]
  exact finiteSupport_converges (stringEnergy a dim k d) (he d) (startSupport a dim d)
end
end ElementaryPositivity.UnitSelections

end
section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity EnergyLaurent
noncomputable section
variable {S T I : Type*} (a : S→ℕ) (dim : S→(I→ℕ)) (k : S→ℤ)
variable (he : ∀d,Admissible (stringEnergy a dim k d))

lemma stringSeries_congr (b : S→ℕ) (dim' : S→(I→ℕ)) (k' : S→ℤ)
    (he' : ∀d,Admissible (stringEnergy b dim' k' d))
    (ha : a=b) (hd : dim=dim') (hk : k=k') :
    stringSeries a dim k he=stringSeries b dim' k' he' := by
  cases ha
  cases hd
  cases hk
  rfl

lemma stringSeries_reindex (e : T ≃ S) (d : I→ℕ) :
    stringSeries (fun s=>a (e s)) (fun s=>dim (e s)) (fun s=>k (e s))
      (stringReindex_admissible e a dim k he) d=stringSeries a dim k he d :=
  series_equiv _ _ (stringReindex e a dim d) (stringReindex_energy e a dim k d)

lemma stringSeries_zero (hdim : ∀s,dim s≠0) : stringSeries a dim k he 0=1 := by
  have hE : ∀f : StringCounts a dim 0,stringEnergy a dim k 0 f=0 :=
    fun f=>dimensionCounts_zero_energy (fun x:S×ℕ=>a x.1≠0) (fun x=>dim x.1)
      (fun x=>hdim x.1) (fun x=>k x.1-2*(x.2:ℤ)) f
  let := dimensionCounts_zero_subsingleton (fun x:S×ℕ=>a x.1≠0) (fun x=>dim x.1) (fun x=>hdim x.1)
  let : Nonempty (StringCounts a dim 0) := ⟨⟨zeroCount _,countDimension_zero _ _⟩⟩
  ext j
  rw [stringSeries,series_coeff,HahnSeries.coeff_one]
  by_cases hj : j=0
  · subst j
    have H : ∀f : StringCounts a dim 0,stringEnergy a dim k 0 f= -0 := by simpa using hE
    simp only [H,neg_zero]
    simp
  · let : IsEmpty {f : StringCounts a dim 0 // stringEnergy a dim k 0 f= -j} :=
      ⟨fun f=>hj (by have HH:=f.property; rw [hE] at HH; omega)⟩
    simp [hj]

lemma stringSeries_empty [IsEmpty S] (d : I→ℕ) (hd : d≠0) : stringSeries a dim k he d=0 := by
  let : IsEmpty (StringCounts a dim d) := ⟨fun f=>by
    apply hd
    rw [←f.property,countDimension]
    exact Finset.sum_eq_zero (fun x _=>isEmptyElim x.1)⟩
  ext j
  rw [stringSeries,series_coeff]
  simp
end
end ElementaryPositivity.UnitSelections

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_SeriesApproximation
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries LaurentPrecision Filter
noncomputable section
variable {M ι : Type*} [AddCommGroup M]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M→+M→+ℤ)

lemma testAgreement_refl (T : Finset (PrecisionTest (M:=M))) (F : PowerSeries (Torus v Ω)) :
    TestAgreement v Ω T F F := fun _ _=>agrees_refl _ _

lemma TestAgreement.trans {T : Finset (PrecisionTest (M:=M))}
    {F G H : PowerSeries (Torus v Ω)}
    (hf : TestAgreement v Ω T F G) (hg : TestAgreement v Ω T G H) :
    TestAgreement v Ω T F H := fun t ht j hj=>(hf t ht j hj).trans (hg t ht j hj)

lemma inPrecisionClosure_self {A : Set (PowerSeries (Torus v Ω))} {F : PowerSeries (Torus v Ω)}
    (hF : F∈A) : InPrecisionClosure v Ω A F :=
  fun T=>⟨F,hF,testAgreement_refl v Ω T F⟩

lemma InPrecisionClosure.mono {A B : Set (PowerSeries (Torus v Ω))} {F : PowerSeries (Torus v Ω)}
    (hF : InPrecisionClosure v Ω A F) (hAB : A⊆B) : InPrecisionClosure v Ω B F := by
  intro T
  obtain ⟨G,hG,H⟩:=hF T
  exact ⟨G,hAB hG,H⟩

variable (l : Filter ι)
lemma SeriesConverges.testAgreement {f : ι→PowerSeries (Torus v Ω)} {F : PowerSeries (Torus v Ω)}
    (hf : SeriesConverges v Ω l f F) (T : Finset (PrecisionTest (M:=M))) :
    ∀ᶠi in l,TestAgreement v Ω T (f i) F := by
  classical
  induction T using Finset.induction_on with
  | empty=>exact Eventually.of_forall (by simp [TestAgreement])
  | @insert t T ht ih=>
    filter_upwards [ih,hf t.1 t.2.1 t.2.2] with i hi hj
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl|ha
    · exact hj
    · exact hi a ha

lemma InPrecisionClosure.of_converges [l.NeBot]
    {A : Set (PowerSeries (Torus v Ω))} {f : ι→PowerSeries (Torus v Ω)}
    {F : PowerSeries (Torus v Ω)} (hf : SeriesConverges v Ω l f F)
    (hA : ∀ᶠi in l,InPrecisionClosure v Ω A (f i)) : InPrecisionClosure v Ω A F := by
  intro T
  obtain ⟨i,hi,hAi⟩:=((hf.testAgreement v Ω l T).and hA).exists
  obtain ⟨G,hG,H⟩:=hAi T
  exact ⟨G,hG,H.trans v Ω hi⟩

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_StringSumProduct
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity EnergyLaurent RawShuffle
noncomputable section
variable {A B I : Type*}
variable (a : A→ℕ) (b : B→ℕ) (da : A→(I→ℕ)) (db : B→(I→ℕ))
variable (ka : A→ℤ) (kb : B→ℤ)

variable [Fintype I] [DecidableEq I]
variable (ha : ∀d,Admissible (stringEnergy a da ka d))
variable (hb : ∀d,Admissible (stringEnergy b db kb d))

lemma stringSum_series (d : I→ℕ) :
    stringSeries (Sum.elim a b) (Sum.elim da db) (Sum.elim ka kb)
      (stringSum_admissible a b da db ka kb ha hb) d=
      ∑s : DimensionSplit d,stringSeries a da ka ha s.left*stringSeries b db kb hb s.right := by
  rw [stringSeries,series_equiv _
    (countSum_admissible (fun x:A×ℕ=>a x.1≠0) (fun x:B×ℕ=>b x.1≠0)
      (fun x=>da x.1) (fun x=>db x.1)
      (fun x=>ka x.1-2*(x.2:ℤ)) (fun x=>kb x.1-2*(x.2:ℤ)) ha hb d)
    (stringSumCounts a b da db d)
    (stringSumCounts_energy a b da db ka kb d)]
  exact countSum_series (fun x:A×ℕ=>a x.1≠0) (fun x:B×ℕ=>b x.1≠0)
    (fun x=>da x.1) (fun x=>db x.1)
    (fun x=>ka x.1-2*(x.2:ℤ)) (fun x=>kb x.1-2*(x.2:ℤ)) ha hb d
end
end ElementaryPositivity.UnitSelections

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_StringRay
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity EnergyLaurent RawShuffle WeightedTorusSeries QuantumTorus WallUnits PowerSeries
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : ℕ) (δ : I→ℕ) (k : ℤ)

lemma oneString_energy (q : Σn,UnitIndex a n) :
    countEnergy (fun _ : PUnit×ℕ=>a≠0) (fun x=>k-2*(x.2:ℤ)) (oneStringEquiv a q)=
      unitEnergy a q.1 k q.2 := by
  dsimp only [countEnergy,oneStringEquiv,Equiv.trans_apply]
  rw [countReindex_sum]
  exact unitRowCount_energy a q.1 k q.2

variable (hδ : δ≠0)

variable (he : ∀d,Admissible (stringEnergy (fun _:PUnit=>a) (fun _=>δ) (fun _=>k) d))

omit [Fintype I] [DecidableEq I] in
include hδ in
lemma oneStringSeries_nsmul (n : ℕ) :
    stringSeries (fun _:PUnit=>a) (fun _=>δ) (fun _=>k) he (n • δ)=indexedUnitSeries a n k := by
  symm
  apply series_equiv _ _ (oneStringDimensionEquiv a δ hδ n)
  intro f
  exact oneString_energy a k ⟨n,f⟩

omit [Fintype I] [DecidableEq I] in
lemma oneStringSeries_off (d : I→ℕ) (hd : ∀n:ℕ,n • δ≠d) :
    stringSeries (fun _:PUnit=>a) (fun _=>δ) (fun _=>k) he d=0 := by
  let : IsEmpty (StringCounts (fun _:PUnit=>a) (fun _=>δ) d) := ⟨fun f=>by
    let q:=(oneStringEquiv a).symm f.val
    apply hd q.1
    rw [←oneString_dimension a δ q]
    dsimp only [q]
    rw [Equiv.apply_symm_apply]
    exact f.property⟩
  ext j
  rw [stringSeries,series_coeff]
  simp only [HahnSeries.coeff_zero,Nat.cast_eq_zero]
  exact Nat.card_eq_zero.mpr (Or.inl (inferInstance : IsEmpty _))
end
end ElementaryPositivity.UnitSelections

end
section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity RawShuffle EnergyLaurent QuantumTorus WeightedTorusSeries WallUnits PowerSeries
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : ℕ) (δ : I→ℕ) (k : ℤ) (hδ : δ≠0)
variable (he : ∀d,Admissible (stringEnergy (fun _:PUnit=>a) (fun _=>δ) (fun _=>k) d))
variable (w : I→ℕ) [Fact (∀i,0<w i)]
variable {M : Type*} [AddCommGroup M] (Ω : M→+M→+ℤ) (P : (I→ℕ)→+M)

omit [DecidableEq I] in
include hδ in
lemma oneString_push_literal :
    push w LaurentRay.vUnit Ω P (stringSeries (fun _:PUnit=>a) (fun _=>δ) (fun _=>k) he)=
      weightedRay LaurentRay.vUnit Ω (WeightedTorusSeries.weight w δ) (P δ)
        (PowerSeries.map LaurentRay.atInfinity (indexedUnit a k)) := by
  apply push_on_ray
  · intro n
    rw [oneStringSeries_nsmul a δ k hδ he,coeff_map,indexedUnit_literal_expansion]
  · exact oneStringSeries_off a δ k he
end
end ElementaryPositivity.UnitSelections

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_StringSumPush
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity EnergyLaurent RawShuffle QuantumTorus WeightedTorusSeries WallUnits PowerSeries
noncomputable section
variable {A B I : Type*} [Fintype I] [DecidableEq I]
variable (a : A→ℕ) (b : B→ℕ) (da : A→(I→ℕ)) (db : B→(I→ℕ))
variable (ka : A→ℤ) (kb : B→ℤ)
variable (ha : ∀d,Admissible (stringEnergy a da ka d))
variable (hb : ∀d,Admissible (stringEnergy b db kb d))
variable (D : AddSubmonoid (I→ℕ)) (hda : ∀s,da s∈D) (hdb : ∀s,db s∈D)
variable (w : I→ℕ) [Fact (∀i,0<w i)]
variable {M : Type*} [AddCommGroup M] (Ω : M→+M→+ℤ) (P : (I→ℕ)→+M)
variable (hiso : ∀d∈D,∀e∈D,Ω (P d) (P e)=0)
include hda hdb hiso in
lemma stringSum_push :
    push w LaurentRay.vUnit Ω P (stringSeries (Sum.elim a b) (Sum.elim da db) (Sum.elim ka kb)
      (stringSum_admissible a b da db ka kb ha hb))=
      push w LaurentRay.vUnit Ω P (stringSeries a da ka ha)*
      push w LaurentRay.vUnit Ω P (stringSeries b db kb hb) := by
  rw [←push_convolution]
  congr 1
  funext d
  rw [convolution_of_isotropic_support LaurentRay.vUnit Ω P _ _ (fun d e hd he=>
    hiso d (stringSeries_support a da ka ha D hda d hd)
      e (stringSeries_support b db kb hb D hdb e he))]
  exact stringSum_series a b da db ka kb ha hb d
end
end ElementaryPositivity.UnitSelections

end
section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity EnergyLaurent RawShuffle QuantumTorus WeightedTorusSeries WallUnits PowerSeries
noncomputable section
variable {A I : Type*} [Fintype I] [DecidableEq I]
variable (a : Option A→ℕ) (dim : Option A→(I→ℕ)) (k : Option A→ℤ)
variable (he : ∀d,Admissible (stringEnergy a dim k d))
variable (D : AddSubmonoid (I→ℕ)) (hdim : ∀s,dim s∈D)
variable (w : I→ℕ) [Fact (∀i,0<w i)]
variable {M : Type*} [AddCommGroup M] (Ω : M→+M→+ℤ) (P : (I→ℕ)→+M)
variable (hiso : ∀d∈D,∀e∈D,Ω (P d) (P e)=0)

lemma option_pullback {T : Type*} (f : Option A→T) :
    (fun s:A⊕PUnit.{1}=>f ((Equiv.optionEquivSumPUnit A).symm s))=
      Sum.elim (fun s=>f (some s)) (fun _=>f none) := by
  funext s
  cases s <;> rfl

local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_r82e08d_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
include hdim hiso in
lemma stringOption_push (h0 : dim none≠0) :
    push w LaurentRay.vUnit Ω P (stringSeries a dim k he)=
      push w LaurentRay.vUnit Ω P
        (stringSeries (fun s=>a (some s)) (fun s=>dim (some s)) (fun s=>k (some s))
          (stringEmbedding_admissible a dim k he someEmbedding))*
      weightedRay LaurentRay.vUnit Ω (WeightedTorusSeries.weight w (dim none)) (P (dim none))
        (PowerSeries.map LaurentRay.atInfinity (indexedUnit (a none) (k none))) := by
  have H:=funext (stringSeries_reindex a dim k he (Equiv.optionEquivSumPUnit A : Option A ≃ A⊕PUnit.{1}).symm)
  let ha:=stringEmbedding_admissible a dim k he someEmbedding
  let hb:=stringEmbedding_admissible a dim k he noneEmbedding
  let hs:=stringSum_admissible (fun s=>a (some s)) (fun _:PUnit.{1}=>a none)
    (fun s=>dim (some s)) (fun _:PUnit.{1}=>dim none)
    (fun s=>k (some s)) (fun _:PUnit.{1}=>k none) ha hb
  have HC:=stringSeries_congr _ _ _
    (stringReindex_admissible (Equiv.optionEquivSumPUnit A : Option A ≃ A⊕PUnit.{1}).symm a dim k he)
    _ _ _ hs (option_pullback a) (option_pullback dim) (option_pullback k)
  rw [←(HC.symm.trans H)]
  have HH:=stringSum_push (fun s=>a (some s)) (fun _:PUnit.{1}=>a none)
    (fun s=>dim (some s)) (fun _:PUnit.{1}=>dim none)
    (fun s=>k (some s)) (fun _:PUnit.{1}=>k none) ha hb D
    (fun s=>hdim (some s)) (fun _=>hdim none) w Ω P hiso
  rw [HH,oneString_push_literal (a none) (dim none) (k none) h0 hb w Ω P]
end
end ElementaryPositivity.UnitSelections

namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity EnergyLaurent RawShuffle QuantumTorus WeightedTorusSeries WallUnits PowerSeries
noncomputable section
variable {S I : Type*} [Fintype I] [DecidableEq I] [IsEmpty S]
variable (a : S→ℕ) (dim : S→(I→ℕ)) (k : S→ℤ)
variable (he : ∀d,Admissible (stringEnergy a dim k d))
variable (w : I→ℕ) [Fact (∀i,0<w i)]
variable {M : Type*} [AddCommGroup M] (Ω : M→+M→+ℤ) (P : (I→ℕ)→+M)

local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_1_r82e08d_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
omit [DecidableEq I] in
lemma stringEmpty_push : push w LaurentRay.vUnit Ω P (stringSeries a dim k he)=1 := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero=>
    rw [coeff_zero_eq_constantCoeff,push_constant w LaurentRay.vUnit Ω P _
      (stringSeries_zero a dim k he (fun s=>isEmptyElim s))]
    simp
  | succ n=>
    simp only [push,coeff_mk,pushCoeff,coeff_one,show n+1≠0 from Nat.succ_ne_zero n,ite_false, if_false]
    apply Finset.sum_eq_zero
    intro d hd
    have H : d.val≠0 := by
      intro hz
      have HH:=d.property
      rw [hz,map_zero] at HH
      omega
    rw [stringSeries_empty a dim k he d.val H,Torus.monomial_zero]
end
end ElementaryPositivity.UnitSelections

end
section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity EnergyLaurent RawShuffle QuantumTorus WeightedTorusSeries WallUnits PowerSeries
noncomputable section
universe u
variable {S : Type u} {I : Type*} [Fintype I] [DecidableEq I]
variable (a : S→ℕ) (dim : S→(I→ℕ)) (k : S→ℤ)
variable (he : ∀d,Admissible (stringEnergy a dim k d))
variable (D : AddSubmonoid (I→ℕ)) (hdim : ∀s,dim s∈D) (h0 : ∀s,dim s≠0)
variable (w : I→ℕ) [Fact (∀i,0<w i)]
variable {M : Type*} [AddCommGroup M] (Ω : M→+M→+ℤ) (P : (I→ℕ)→+M)
variable (hiso : ∀d∈D,∀e∈D,Ω (P d) (P e)=0)

include hdim h0 hiso in
theorem finiteString_literal [Finite S] :
    ∃l : List S,l.Nodup ∧ (∀s,s∈l) ∧
      push w LaurentRay.vUnit Ω P (stringSeries a dim k he)=
        (l.map (stringLiteralUnit a dim k w Ω P)).prod := by
  classical
  revert a dim k
  induction S using Finite.induction_empty_option with
  | @of_equiv A B e ih =>
    intro a dim k he hdim h0
    let heA:=stringReindex_admissible e a dim k he
    obtain ⟨l,hl,hall,H⟩:=ih (fun s=>a (e s)) (fun s=>dim (e s)) (fun s=>k (e s))
      heA (fun s=>hdim (e s)) (fun s=>h0 (e s))
    refine ⟨l.map e,hl.map e.injective,?_,?_⟩
    · intro s
      exact List.mem_map.mpr ⟨e.symm s,hall (e.symm s),e.apply_symm_apply s⟩
    · rw [List.map_map]
      change push w LaurentRay.vUnit Ω P (stringSeries a dim k he) =
        (l.map (stringLiteralUnit (fun s=>a (e s)) (fun s=>dim (e s))
          (fun s=>k (e s)) w Ω P)).prod
      rw [←H]
      congr 1
      exact (funext (stringSeries_reindex a dim k he e)).symm
  | h_empty =>
    intro a dim k he hdim h0
    refine ⟨[],by simp,fun s=>isEmptyElim s,?_⟩
    simpa using stringEmpty_push a dim k he w Ω P
  | @h_option A inst ih =>
    intro a dim k he hdim h0
    let heA:=stringEmbedding_admissible a dim k he someEmbedding
    obtain ⟨l,hl,hall,H⟩:=ih (fun s=>a (some s)) (fun s=>dim (some s)) (fun s=>k (some s))
      heA (fun s=>hdim (some s)) (fun s=>h0 (some s))
    refine ⟨l.map some++[none],?_,?_,?_⟩
    · rw [List.nodup_append]
      refine ⟨hl.map (Option.some_injective _),by simp,?_⟩
      simp
    · intro s
      cases s with
      | none=>simp
      | some s=>simp [hall s]
    · rw [stringOption_push a dim k he D hdim w Ω P hiso (h0 none)]
      rw [H,List.map_append,List.prod_append,List.map_map,List.map_singleton,List.prod_singleton]
      rfl
end
end ElementaryPositivity.UnitSelections

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_WeightedCompletion
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.WeightedTorusSeries
open QuantumTorus PowerSeries LaurentPrecision
noncomputable section
variable {I J M ι : Type*} [Fintype I] [DecidableEq I] [Fintype J] [AddCommGroup M]
variable (w : I→ℕ) [Fact (∀i,0<w i)]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M→+M→+ℤ) (P : (I→ℕ)→+M)
variable (C : (J→ℤ)→+M) (hroot : ∀d,HasRootDegree C (weight w d) (P d))

local instance instRingTorusLaurentSeriesRat_r82e08d_1 : Ring (Torus v Ω) := Torus.instRing v Ω
attribute [local instance] OAI.ElementaryPositivity.WeightedTorusSeries.instAddCommMonoidTorusLaurentSeriesRat
local instance instAddGroupTorusLaurentSeriesRat_r82e08d_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
lemma torus_sum_apply {α : Type*} (s : Finset α) (f : α→Torus v Ω) (m : M) :
    (∑a∈s,f a) m=∑a∈s,f a m := by
  classical
  induction s using Finset.induction_on with
  | empty=>rfl
  | @insert a s ha ih=>
    rw [Finset.sum_insert ha,Finset.sum_insert ha]
    change (f a) m+(∑i∈s,f i) m=_
    rw [ih]

variable (l : Filter ι)
omit [DecidableEq I] in
lemma push_converges {f : ι→(I→ℕ)→LaurentSeries ℚ} {F : (I→ℕ)→LaurentSeries ℚ}
    (hf : ∀d,Converges l (fun i=>f i d) (F d)) :
    SeriesConverges v Ω l (fun i=>push w v Ω P (f i)) (push w v Ω P F) := by
  classical
  intro n m
  simp only [push,coeff_mk,pushCoeff,torus_sum_apply]
  apply LaurentPrecision.Converges.sum
  intro d hd
  change Converges l (fun i=>(Finsupp.single (P d.val) (f i d.val)) m)
    ((Finsupp.single (P d.val) (F d.val)) m)
  by_cases H : m=P d.val
  · subst m
    simpa only [Finsupp.single_eq_same] using hf d.val
  · simp only [Finsupp.single_eq_of_ne H]
    exact converges_const l 0
end
end ElementaryPositivity.WeightedTorusSeries

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_StringLiteralClosure
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity RawShuffle EnergyLaurent QuantumTorus WeightedTorusSeries WallUnits PowerSeries
noncomputable section
variable {S I : Type*} [Fintype I] [DecidableEq I]
variable (a : S→ℕ) (dim : S→(I→ℕ)) (k : S→ℤ)
variable (he : ∀d,Admissible (stringEnergy a dim k d))
variable (D : AddSubmonoid (I→ℕ)) (hdim : ∀s,dim s∈D) (h0 : ∀s,dim s≠0)
variable (w : I→ℕ) [Fact (∀i,0<w i)]
variable {M : Type*} [AddCommGroup M] (Ω : M→+M→+ℤ) (P : (I→ℕ)→+M)
variable (hiso : ∀d∈D,∀e∈D,Ω (P d) (P e)=0)

include h0 hdim hiso in
lemma finiteStart_literal (T : Finset S) :
    push w LaurentRay.vUnit Ω P (finiteStartSeries a dim k he T)∈finiteStringProducts a dim k w Ω P := by
  classical
  obtain ⟨l,hl,hall,H⟩:=finiteString_literal (fun s:T=>a s.val) (fun s:T=>dim s.val)
    (fun s:T=>k s.val) (finiteStart_admissible a dim k he T) D (fun s=>hdim s.val)
    (fun s=>h0 s.val) w Ω P hiso
  refine ⟨l.map Subtype.val,hl.map Subtype.val_injective,?_⟩
  rw [List.map_map]
  change push w LaurentRay.vUnit Ω P (stringSeries (fun s:T=>a s.val)
    (fun s:T=>dim s.val) (fun s:T=>k s.val) (finiteStart_admissible a dim k he T)) =
      (l.map (stringLiteralUnit (fun s:T=>a s.val) (fun s:T=>dim s.val)
        (fun s:T=>k s.val) w Ω P)).prod
  exact H

include h0 hdim hiso in

theorem stringLiteral_closure :
    InPrecisionClosure LaurentRay.vUnit Ω (finiteStringProducts a dim k w Ω P)
      (push w LaurentRay.vUnit Ω P (stringSeries a dim k he)) := by
  apply InPrecisionClosure.of_converges LaurentRay.vUnit Ω (Filter.atTop : Filter (Finset S))
    (push_converges w LaurentRay.vUnit Ω P Filter.atTop
      (finiteStartSeries_converges a dim k he))
  exact Filter.Eventually.of_forall (fun T=>inPrecisionClosure_self LaurentRay.vUnit Ω
    (finiteStart_literal a dim k he D hdim h0 w Ω P hiso T))
end
end ElementaryPositivity.UnitSelections

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_StringRootClosure
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity RawShuffle EnergyLaurent QuantumTorus WeightedTorusSeries WallUnits PowerSeries
noncomputable section
variable {S I J M : Type*} [Fintype I] [DecidableEq I] [Fintype J] [AddCommGroup M]
variable (a : S→ℕ) (dim : S→(I→ℕ)) (k : S→ℤ)
variable (he : ∀d,Admissible (stringEnergy a dim k d))
variable (D : AddSubmonoid (I→ℕ)) (hdim : ∀s,dim s∈D) (h0 : ∀s,dim s≠0)
variable (w : I→ℕ) [Fact (∀i,0<w i)]
variable (Ω : M→+M→+ℤ) (P : (I→ℕ)→+M) (C : (J→ℤ)→+M)
variable (hiso : ∀d∈D,∀e∈D,Ω (P d) (P e)=0)
variable (V : M→Prop) (hr : ∀s,HasRootDegree C (WeightedTorusSeries.weight w (dim s)) (P (dim s)))
variable (hv : ∀s,V (P (dim s)))

omit [DecidableEq I] in
include h0 hr hv in
lemma finiteStringProducts_rootProducts :
    finiteStringProducts a dim k w Ω P ⊆ literalRootProducts Ω C V := by
  rintro F ⟨l,hl,rfl⟩
  refine ⟨l.map (stringWallDatum a dim k w P),?_,?_⟩
  · intro u hu
    obtain ⟨s,hs,rfl⟩:=List.mem_map.mp hu
    exact ⟨weight_pos w (dim s) (h0 s),hr s,hv s⟩
  · rw [List.map_map]
    rfl

include h0 hdim hiso hr hv in
theorem stringRoot_closure :
    InPrecisionClosure LaurentRay.vUnit Ω (literalRootProducts Ω C V)
      (push w LaurentRay.vUnit Ω P (stringSeries a dim k he)) :=
  (stringLiteral_closure a dim k he D hdim h0 w Ω P hiso).mono LaurentRay.vUnit Ω
    (finiteStringProducts_rootProducts a dim k h0 w Ω P C V hr hv)
end
end ElementaryPositivity.UnitSelections

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_PrimitiveRootClosure
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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
variable (w : I→ℕ) [Fact (∀i,0<w i)]
variable (Ω : M→+M→+ℤ) (P : (I→ℕ)→+M) (C : (J→ℤ)→+M)
variable (hgeom : ∀d e,Ω (P d) (P e)=eulerForm a d e-eulerForm a e d)
variable (hroot : ∀d,HasRootDegree C (WeightedTorusSeries.weight w d) (P d))
variable (θ : ℝ) (V : M→Prop) (hv : ∀d∈slopeDimensions c η hc θ,V (P d))

include hgeom hroot hv in
lemma primitiveFactor_rootClosure :
    InPrecisionClosure LaurentRay.vUnit Ω (literalRootProducts Ω C V)
      (push w LaurentRay.vUnit Ω P (primitiveCountsSeries a κ c η hc θ)) := by
  let dim : SlopeStringStart a c η hc θ → (I→ℕ) := fun s=>s.1.val.1.val
  have hdim : ∀s,dim s∈slopeDimensions c η hc θ := fun s=>s.1.val.1.property
  have hi : ∀d∈slopeDimensions c η hc θ,∀e∈slopeDimensions c η hc θ,Ω (P d) (P e)=0 := by
    intro d hd e he
    rw [hgeom,eulerForm_slopeDimensions_symm a c η hc θ ⟨d,hd⟩ ⟨e,he⟩,sub_self]
  exact stringRoot_closure (slopeStartRowType a c η hc θ) dim
    (slopeStartParameter a κ c η hc θ) (primitiveCountsEnergy_admissible a κ c η hc θ)
    (slopeDimensions c η hc θ) hdim (fun s=>s.1.property) w Ω P C hi V
    (fun s=>hroot (dim s)) (fun s=>hv _ (hdim s))

variable (h : M→+ℝ) (hh : ∀d,h (P d)=slopeValue c η θ d)
include hgeom hroot hv hh in
theorem finiteInput_zero_rootClosure_oai (ε : I→Bool) (ha : ∀i,a i i=elementaryDiagonal ε i) :
    InPrecisionClosure LaurentRay.vUnit Ω (literalRootProducts Ω C V)
      (PowerSeriesSplit.zeroFactor (positiveProject LaurentRay.vUnit Ω h)
        (zeroProject LaurentRay.vUnit Ω h)
        (push w LaurentRay.vUnit Ω P (literalInputCoefficient a κ ε))) := by
  rw [←literalInput_primitiveFactor a κ c η hc w Ω P hgeom h θ hh ε ha]
  exact primitiveFactor_rootClosure a κ c η hc w Ω P C hgeom hroot θ V hv
end
end ElementaryPositivity.RawShuffle

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.ElementaryPositivity.RawShuffle.finiteInput_zero_rootClosure_oai.{u_1, u_2, u_3} := @OAI.ElementaryPositivity.RawShuffle.finiteInput_zero_rootClosure_oai.{u_1, u_2, u_3}
