-- Prove2me | solution 1 for OAI.ElementaryPositivity.RawShuffle.literalInput_primitiveFactor
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T20:09:00.562337+00:00
-- url     : https://prove2.me/submissions/766ea19b-c57b-4166-94b0-a9dde6f063f6

import Mathlib
import Definitions.Def_OAIQ368Chrom007
import Definitions.Def_OAIQ368Chrom055
import Definitions.Def_OAIQ368Chrom056

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
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq _root_.OAI.ElementaryPositivity.RawShuffle.globalStringIndexLinearOrder _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceZeroUnique
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
section
namespace ElementaryPositivity.EnergyLaurent
open scoped LaurentSeries
noncomputable section

lemma series_fin_pi (n : ℕ) (A : Fin n → Type*) (e : ∀i,A i → ℤ)
    (he : ∀i,Admissible (e i)) :
    (∏i,series (e i) (he i))=
      series (fun f : ∀i,A i=>∑i,e i (f i)) (admissible_fin_pi n A e he) := by
  induction n with
  | zero =>
    simp only [Fin.prod_univ_zero]
    have hu : Unique (∀i:Fin 0,A i):=⟨⟨fun i=>Fin.elim0 i⟩,fun _=>Subsingleton.elim _ _⟩
    let := hu
    change 1=(family _ _).hsum
    rw [HahnSeries.SummableFamily.hsum_unique]
    change 1=HahnSeries.single 0 (1:ℚ)
    exact HahnSeries.single_zero_one.symm
  | succ n ih =>
    rw [Fin.prod_univ_succ,ih (fun i=>A i.succ) (fun i=>e i.succ) (fun i=>he i.succ),series_mul]
    apply series_equiv _ _ (finSuccPi n A).symm
    intro f
    change (∑i,e i (Fin.cases f.1 f.2 i))=e 0 f.1+∑i,e i.succ (f.2 i)
    rw [Fin.sum_univ_succ]
    rfl
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
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_FintypeEnergyProduct
attribute [-instance] _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
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
variable {I : Type*} [Fintype I] (A : I → Type*) (e : ∀i,A i → ℤ)

lemma series_pi (he : ∀i,Admissible (e i)) :
    (∏i,series (e i) (he i))=series (fun f : ∀i,A i=>∑i,e i (f i)) (admissible_pi A e he) := by
  rw [←(Fintype.equivFin I).symm.prod_comp (fun i=>series (e i) (he i))]
  rw [series_fin_pi]
  exact series_equiv _ _ (finitePiReindex A) (finitePiReindex_energy A e)
end
end ElementaryPositivity.EnergyLaurent
end
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
local instance instAddGroupTorus_rfdb662_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FiniteReorderingEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic
attribute [local instance] Classical.propDecidable

lemma card_fibres_injective_regrade {X Y : Type*} (f : X → ℤ) (g : Y → ℤ)
    (n : ℤ → ℤ) (hn : Function.Injective n)
    (h : ∀ k,Nat.card {x : X // f x=k}=Nat.card {y : Y // g y=k}) (e : ℤ) :
    Nat.card {x : X // n (f x)=e}=Nat.card {y : Y // n (g y)=e} := by
  by_cases H : ∃ k,n k=e
  · obtain ⟨k,hk⟩:=H
    let ex : {x : X // n (f x)=e} ≃ {x : X // f x=k} :=
      Equiv.subtypeEquivRight (fun x=>by rw [←hk,hn.eq_iff])
    let ey : {y : Y // n (g y)=e} ≃ {y : Y // g y=k} :=
      Equiv.subtypeEquivRight (fun y=>by rw [←hk,hn.eq_iff])
    rw [Nat.card_congr ex,Nat.card_congr ey]
    exact h k
  · let : IsEmpty {x : X // n (f x)=e} := ⟨fun x=>H ⟨f x.val,x.property⟩⟩
    let : IsEmpty {y : Y // n (g y)=e} := ⟨fun y=>H ⟨g y.val,y.property⟩⟩
    simp

universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
  [hχ : Fact (∀ θ,SlopeEulerSymmetric a c η θ)]

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.energySlopeSymmetricFact
theorem finiteReordering_energyCoefficient (ε : I → Bool)
    (ha : ∀ i,a i i=elementaryDiagonal ε i) (d : I → ℕ) (e : ℤ) :
    Nat.card {x : InputIndexLists ε d // inputTorusEnergy a κ ε d x=e}=
      Nat.card (OutputEnergyCoefficient a κ c η hc d e) := by
  let ex : {x : SortedPackExponent d // normalizedEnergy a κ d (sortedPackDegree d x)=e} ≃
      {x : InputIndexLists ε d // inputTorusEnergy a κ ε d x=e} :=
    (inputListEquiv ε d).subtypeEquiv (by intro x; rw [inputListEnergy_normalized a κ ε d ha])
  let ey : OutputEnergyCoefficient a κ c η hc d e ≃
      {i : Σ l : HNIndex c η d,HNStringIndex a c η hc l.val //
        normalizedEnergy a κ d (hnStringDegree a c η hc i.1.val i.2)=e} :=
    Equiv.subtypeEquivRight (by
      intro i
      rw [hnStringEnergy_normalized,i.1.property.1])
  rw [←Nat.card_congr ex,Nat.card_congr ey]
  exact card_fibres_injective_regrade _ _ _ (normalizedEnergy_injective a κ d)
    (finiteStringReordering_coefficient a c η hc d) e
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic
attribute [local instance] Classical.propDecidable
universe u

variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
  [hχ : Fact (∀ θ,SlopeEulerSymmetric a c η θ)]

local instance finiteLaurentSlopeFact_rfdb662_1 (θ : ℝ) : Fact (SlopeEulerSymmetric a c η θ) := ⟨hχ.out θ⟩
theorem finiteReordering_laurent (ε : I → Bool)
    (ha : ∀i,a i i=elementaryDiagonal ε i) (d : I → ℕ) :
    inputReorderingSeries a κ ε ha d=outputReorderingSeries a κ c η hc d := by
  apply EnergyLaurent.series_eq_of_cards
  exact finiteReordering_energyCoefficient a κ c η hc ε ha d

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_PrimitiveBlockRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic UnitSelections
noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0 < c i)
  [hχ : Fact (∀ θ,SlopeEulerSymmetric a c η θ)]

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.blockRowsFact
theorem finiteReordering_rows (ε : I → Bool) (ha : ∀i,a i i=elementaryDiagonal ε i) (d : I → ℕ) :
    inputReorderingSeries a κ ε ha d=outputRowsSeries a κ c η hc d := by
  rw [finiteReordering_laurent a κ c η hc ε ha]
  exact EnergyLaurent.series_equiv _ _ (outputRowsEquiv a c η hc d)
    (fun w=>hnRowsEquiv_energy a κ c η hc w.1.val w.2)
end
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic
noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0 < c i)
  [hχ : Fact (∀ θ,SlopeEulerSymmetric a c η θ)]

local instance decoratedFact_rfdb662_1 (θ : ℝ) : Fact (SlopeEulerSymmetric a c η θ) := ⟨hχ.out θ⟩
lemma decoratedEnergy_append (l r : List (RowBlock a c η hc)) :
    decoratedEnergy a κ c η hc (l++r)=
      decoratedEnergy a κ c η hc l+decoratedEnergy a κ c η hc r+
        (eulerForm a (decoratedDimension a c η hc l) (decoratedDimension a c η hc r)-
          eulerForm a (decoratedDimension a c η hc r) (decoratedDimension a c η hc l)) := by
  induction l with
  | nil=>simp [decoratedEnergy,decoratedDimension,eulerForm]
  | cons b l ih=>
    simp only [List.cons_append,decoratedEnergy,ih,
      decoratedDimension,List.map_cons,List.sum_cons,List.map_append,List.sum_append,eulerForm_add_left,eulerForm_add_right]
    ring

end
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_HNThreshold
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic
noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0 < c i)
  [Fact (∀ θ,SlopeEulerSymmetric a c η θ)]

lemma thresholdIndexEquiv_symm_energy (θ : ℝ) (d : I → ℕ)
    (z : Σ s : DimensionSplit d,HighHNIndex a c η hc θ s.left × LowHNIndex a c η hc θ s.right) :
    decoratedEnergy a κ c η hc ((thresholdIndexEquiv a c η hc θ d).symm z).val=
      decoratedEnergy a κ c η hc z.2.1.val.val.val+
        decoratedEnergy a κ c η hc z.2.2.val.val.val+
        (eulerForm a z.1.left z.1.right-eulerForm a z.1.right z.1.left) := by
  change decoratedEnergy a κ c η hc (z.2.1.val.val.val++z.2.2.val.val.val)=_
  rw [decoratedEnergy_append,z.2.1.property,z.2.2.property]

lemma thresholdIndexEquiv_energy (θ : ℝ) (d : I → ℕ) (w : DecoratedHN a c η hc d) :
    let z:=thresholdIndexEquiv a c η hc θ d w
    decoratedEnergy a κ c η hc z.2.1.val.val.val+
      decoratedEnergy a κ c η hc z.2.2.val.val.val+
      (eulerForm a z.1.left z.1.right-eulerForm a z.1.right z.1.left)=
        decoratedEnergy a κ c η hc w.val := by
  simpa only [Equiv.symm_apply_apply] using
    (thresholdIndexEquiv_symm_energy a κ c η hc θ d (thresholdIndexEquiv a c η hc θ d w)).symm

end
end ElementaryPositivity.RawShuffle

end
section

namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic EnergyLaurent
noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0 < c i)
  [Fact (∀ θ,SlopeEulerSymmetric a c η θ)]

lemma hnSeries_threshold (θ : ℝ) (d : I → ℕ) :
    hnSeries a κ c η hc d = ∑s : DimensionSplit d,
      highSeries a κ c η hc θ s.left * lowSeries a κ c η hc θ s.right *
        HahnSeries.single (-(eulerForm a s.left s.right-eulerForm a s.right s.left)) 1 := by
  let f := fun s : DimensionSplit d=>fun p : HighHNIndex a c η hc θ s.left × LowHNIndex a c η hc θ s.right=>
    highEnergy a κ c η hc θ s.left p.1+lowEnergy a κ c η hc θ s.right p.2+
      (eulerForm a s.left s.right-eulerForm a s.right s.left)
  have hf : ∀s,Admissible (f s) := fun s=>
    admissible_shift (admissible_prod (highEnergy_admissible a κ c η hc θ s.left)
      (lowEnergy_admissible a κ c η hc θ s.right)) _
  have H := series_equiv (decoratedEnergy_admissible a κ c η hc d)
    (admissible_sigma f hf) (thresholdIndexEquiv a c η hc θ d)
    (thresholdIndexEquiv_energy a κ c η hc θ d)
  rw [series_sigma f hf] at H
  change hnSeries a κ c η hc d=_ at H
  rw [H]
  apply Finset.sum_congr rfl
  intro s hs
  dsimp only [f]
  rw [series_shift (admissible_prod (highEnergy_admissible a κ c η hc θ s.left)
    (lowEnergy_admissible a κ c η hc θ s.right)),
    ←series_mul (highEnergy_admissible a κ c η hc θ s.left) (lowEnergy_admissible a κ c η hc θ s.right)]
  rfl

end
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_HNSlope
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic EnergyLaurent
noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable {I : Type u} [Fintype I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0 < c i)
  [Fact (∀ θ,SlopeEulerSymmetric a c η θ)]

include hc in
lemma slopeValue_pos_iff (θ : ℝ) (d : I → ℕ) (hd : d≠0) :
    0 < slopeValue c η θ d ↔ θ < slope c η d := by
  rw [slopeValue,sub_pos,SlopeArithmetic.slope,lt_div_iff₀ (mass_pos c hc d hd)]

variable [DecidableEq I]

lemma decorated_zero_empty (w : DecoratedHN a c η hc 0) : w.val=[] := by
  have H:=HNComposition.length_le 0
    (⟨w.val.map Sigma.fst,⟨w.property.1,w.property.2.1⟩⟩ : HNComposition (0 : I→ℕ))
  simpa only [List.length_map,hnSize_zero,Nat.le_zero,List.length_eq_zero_iff] using H

lemma high_zero_unique (θ : ℝ) (w : HighHNIndex a c η hc θ 0) : w=highEmpty a c η hc θ := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact decorated_zero_empty a c η hc (highDecorated a c η hc θ 0 w)
lemma low_zero_unique (θ : ℝ) (w : LowHNIndex a c η hc θ 0) : w=lowEmpty a c η hc θ := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact decorated_zero_empty a c η hc (lowDecorated a c η hc θ 0 w)

lemma highSeries_zero (θ : ℝ) : highSeries a κ c η hc θ 0=1 := by
  let : Unique (HighHNIndex a c η hc θ 0):=⟨⟨highEmpty a c η hc θ⟩,high_zero_unique a c η hc θ⟩
  change (family _ _).hsum=1
  rw [HahnSeries.SummableFamily.hsum_unique]
  change HahnSeries.single (-(0:ℤ)) (1:ℚ)=1
  simp
lemma lowSeries_zero (θ : ℝ) : lowSeries a κ c η hc θ 0=1 := by
  let : Unique (LowHNIndex a c η hc θ 0):=⟨⟨lowEmpty a c η hc θ⟩,low_zero_unique a c η hc θ⟩
  change (family _ _).hsum=1
  rw [HahnSeries.SummableFamily.hsum_unique]
  change HahnSeries.single (-(0:ℤ)) (1:ℚ)=1
  simp

lemma decorated_value_pos (θ : ℝ) (l : List (RowBlock a c η hc)) (hl : l≠[])
    (h : ∀b∈l,0 < slopeValue c η θ b.1) :
    0 < slopeValue c η θ (decoratedDimension a c η hc l) := by
  induction l with
  | nil=>exact (hl rfl).elim
  | cons b l ih=>
    change 0 < slopeValue c η θ (b.1+decoratedDimension a c η hc l)
    rw [slopeValue_add]
    have hb:=h b (by simp)
    by_cases hnil : l=[]
    · subst l
      simpa [decoratedDimension] using hb
    · exact add_pos hb (ih hnil (fun e he=>h e (by simp [he])))

lemma highIndex_sign (θ : ℝ) (d : I → ℕ) (w : HighHNIndex a c η hc θ d) :
    d=0 ∨ 0 < slopeValue c η θ d := by
  by_cases H : w.val.val.val=[]
  · left
    simpa only [H,decoratedDimension,List.map_nil,List.sum_nil] using w.property.symm
  · right
    rw [←w.property]
    exact decorated_value_pos a c η hc θ _ H (fun b hb=>
      (slopeValue_pos_iff c η hc θ b.1 (w.val.val.property.1 b hb)).mpr (w.val.property b hb))

lemma lowIndex_sign (θ : ℝ) (d : I → ℕ) (w : LowHNIndex a c η hc θ d) :
    slopeValue c η θ d≤0 := by
  rw [←w.property]
  exact decorated_value_nonpos a c η hc θ _ (fun b hb=>
    (slopeValue_nonpos_iff c η hc θ b.1 (w.val.val.property.1 b hb)).mpr (w.val.property b hb))

end
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open UnitSelections EnergyLaurent WallUnits
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I]
variable (a : I → I → ℕ) (κ : I → ℤ) (ε : I → Bool)

lemma inputUnit_energy (d : I → ℕ) (x : InputIndexLists ε d) :
    (∑i,unitEnergy (elementaryDiagonal ε i) (d i) (κ i) (inputUnitEquiv ε d x i))+
      crossInteraction a d=inputTorusEnergy a κ ε d x := by
  simp only [unitEnergy,unitWeight,weight,inputUnitEquiv,Equiv.piCongrRight_apply,Pi.map,
    Equiv.subtypeEquivRight_apply,inputTorusEnergy,inputLinearEnergy,
    listIndexSum,Nat.cast_sum,Finset.sum_sub_distrib,←Finset.mul_sum]
  congr 1
  apply congrArg₂ (·-·)
  · apply Finset.sum_congr rfl; intro i hi; ring
  · rfl

theorem literalInputCoefficient_eq (ha : ∀i,a i i=elementaryDiagonal ε i) (d : I → ℕ) :
    literalInputCoefficient a κ ε d=inputReorderingSeries a κ ε ha d := by
  unfold literalInputCoefficient
  simp only [indexedUnit_literal_expansion,indexedUnitSeries]
  rw [series_pi]
  rw [←series_shift]
  apply series_equiv _ _ (inputUnitEquiv ε d).symm
  intro x
  have H:=inputUnit_energy a κ ε d ((inputUnitEquiv ε d).symm x)
  simpa only [Equiv.apply_symm_apply] using H.symm
end
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_HNSeries
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.EnergyLaurent
noncomputable section
lemma series_eq_zero_of_isEmpty {A : Type*} [IsEmpty A] (e : A → ℤ) (he : Admissible e) :
    series e he=0 := by
  ext j
  simp [series_coeff]
end
end ElementaryPositivity.EnergyLaurent

namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic EnergyLaurent
noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0 < c i)
  [Fact (∀ θ,SlopeEulerSymmetric a c η θ)]

lemma highSeries_support (θ : ℝ) (d : I → ℕ) (hd : highSeries a κ c η hc θ d≠0) :
    d=0 ∨ 0 < slopeValue c η θ d := by
  by_contra H
  let : IsEmpty (HighHNIndex a c η hc θ d) := ⟨fun x=>H (highIndex_sign a c η hc θ d x)⟩
  exact hd (series_eq_zero_of_isEmpty _ _)
lemma lowSeries_support (θ : ℝ) (d : I → ℕ) (hd : lowSeries a κ c η hc θ d≠0) :
    slopeValue c η θ d≤0 := by
  by_contra H
  let : IsEmpty (LowHNIndex a c η hc θ d) := ⟨fun x=>H (lowIndex_sign a c η hc θ d x)⟩
  exact hd (series_eq_zero_of_isEmpty _ _)

lemma literalInput_hnSeries (ε : I → Bool) (ha : ∀i,a i i=elementaryDiagonal ε i) (d : I → ℕ) :
    literalInputCoefficient a κ ε d=hnSeries a κ c η hc d := by
  rw [literalInputCoefficient_eq a κ ε ha,finiteReordering_rows a κ c η hc ε ha]
  exact series_equiv _ _ (decorateOutput a c η hc d)
    (fun x=>decoratedEnergy_rows a κ c η hc x.1.val x.2)

end
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.WeightedTorusSeries
open ElementaryPositivity.RawShuffle ElementaryPositivity.QuantumTorus PowerSeries
noncomputable section
universe u
variable {I : Type u} [Fintype I]
variable (w : I → ℕ) [hw : Fact (∀i,0<w i)]

variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (P : (I → ℕ) →+ M)

attribute [local instance] OAI.ElementaryPositivity.WeightedTorusSeries.instAddCommMonoidTorus_1
lemma pushCoeff_zero (f : (I→ℕ) → R) :
    pushCoeff w v Ω P f 0=Torus.monomial v Ω 0 (f 0) := by
  classical
  rw [pushCoeff,Fintype.sum_unique]
  change Torus.monomial v Ω (P 0) (f 0)=_
  rw [map_zero]
lemma push_constant (f : (I→ℕ) → R) (hf : f 0=1) : constantCoeff (push w v Ω P f)=1 := by
  rw [push,constantCoeff_mk,pushCoeff_zero,hf]
  rfl

lemma project_push_fixed (h : M →+ ℝ) (f : (I→ℕ) → R)
    (hf : ∀d,f d≠0 → d=0 ∨ 0<h (P d)) (n : ℕ) :
    positiveProject v Ω h (coeff (n+1) (push w v Ω P f))=coeff (n+1) (push w v Ω P f) := by
  classical
  simp only [push,coeff_mk,pushCoeff,map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  change (Finsupp.filterAddHom (fun m=>0<h m) : Torus v Ω →+ Torus v Ω) _=_
  rw [filter_monomial]
  by_cases H : f d.val=0
  · simp [H,Torus.monomial_zero]
  · have hp : 0<h (P d.val) := (hf d.val H).resolve_left (by
      intro hz
      have hh:=d.property
      rw [hz,map_zero] at hh
      omega)
    simp only [hp,ite_true, if_true]

lemma project_push_killed (h : M →+ ℝ) (f : (I→ℕ) → R)
    (hf : ∀d,f d≠0 → h (P d)≤0) (n : ℕ) :
    positiveProject v Ω h (coeff n (push w v Ω P f))=0 := by
  classical
  simp only [push,coeff_mk,pushCoeff,map_sum]
  apply Finset.sum_eq_zero
  intro d hd
  change (Finsupp.filterAddHom (fun m=>0<h m) : Torus v Ω →+ Torus v Ω) _=0
  rw [filter_monomial]
  by_cases H : f d.val=0
  · simp [H,Torus.monomial_zero]
  · simp only [not_lt.mpr (hf d.val H),ite_false, if_false]

end
end ElementaryPositivity.WeightedTorusSeries

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_ProjectionRecursion
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.PowerSeriesSplit
open PowerSeries
noncomputable section
variable {R : Type*} [Ring R]

lemma left_coeff_projection (Q : R →+ R) (S : Subring R)
    (hQ : ∀x,Q (Q x)=Q x) (hOne : Q 1=1)
    (hMem : ∀x∈S,Q x∈S)
    (hMul : ∀x∈S,∀y∈S,Q (x*y)=Q x*Q y)
    (f : PowerSeries R) (hf : constantCoeff f=1) (hS : ∀n,coeff n f∈S) (n : ℕ) :
    coeff n (leftFactor Q f)=Q (coeff n f) := by
  have hs:=factors_mem Q S hMem f hS
  cases n with
  | zero => simp only [coeff_zero_eq_constantCoeff_apply,left_constant,hf,hOne]
  | succ n =>
    conv_lhs => rw [leftFactor,coeff_mk,pairCoefficients]
    have hleft (k : ℕ) : coeff k (leftFactor Q f)=(pairCoefficients Q f k).1 := by simp only [leftFactor,coeff_mk]
    have hright (k : ℕ) : coeff k (rightFactor Q f)=(pairCoefficients Q f k).2 := by simp only [rightFactor,coeff_mk]
    simp only [←hleft,←hright]
    change Q (coeff (n+1) f-∑i : Fin n,
      coeff (i.val+1) (leftFactor Q f)*coeff (n-i.val) (rightFactor Q f))=Q (coeff (n+1) f)
    rw [map_sub,map_sum]
    suffices H : (∑i : Fin n,Q (coeff (i.val+1) (leftFactor Q f)*
        coeff (n-i.val) (rightFactor Q f)))=0 by rw [H,sub_zero]
    apply Finset.sum_eq_zero
    intro i hi
    rw [hMul _ (hs.1 (i.val+1)) _ (hs.2 (n-i.val))]
    have he : n-i.val=(n-i.val-1)+1 := by omega
    rw [he,right_killed Q hQ,mul_zero]
end
end ElementaryPositivity.PowerSeriesSplit

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_TorusProjection
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries ElementaryPositivity.WeightedTorusSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (h : M →+ ℝ)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instAddCommMonoidTorus
lemma zeroFactor_coeff_projection (f : PowerSeries (Torus v Ω)) (n : ℕ) :
    coeff n (PowerSeriesSplit.zeroFactor (positiveProject v Ω h) (zeroProject v Ω h) f)=
      zeroProject v Ω h (coeff n (PowerSeriesSplit.rightFactor (positiveProject v Ω h) f)) := by
  apply PowerSeriesSplit.left_coeff_projection (zeroProject v Ω h)
    (supportedSubring v Ω (nonpositiveCone h)) (zeroProject_idem v Ω h) (zeroProject_one v Ω h)
  · intro x hx
    exact (nonpositive_iff v Ω h _).mpr (positive_zero_project v Ω h x)
  · intro x hx y hy
    exact zeroProject_mul_nonpositive v Ω h x y hx hy
  · exact PowerSeriesSplit.right_constant _ _
  · intro k
    cases k with
    | zero => rw [coeff_zero_eq_constantCoeff_apply,PowerSeriesSplit.right_constant]; exact Subring.one_mem _
    | succ k =>
      exact (nonpositive_iff v Ω h _).mpr
        (PowerSeriesSplit.right_killed _ (positiveProject_idem v Ω h) f k)

end
end ElementaryPositivity.QuantumTorus

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
open SlopeArithmetic EnergyLaurent
noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0 < c i)
  [Fact (∀ θ,SlopeEulerSymmetric a c η θ)]

lemma lowSeries_on_slope (θ : ℝ) (d : I → ℕ) (hd : d≠0) (hs : slope c η d=θ) :
    lowSeries a κ c η hc θ d=series (blockRowsEnergy a κ c η hc d)
      (blockRowsEnergy_admissible a κ c η hc d hd) := by
  symm
  exact series_equiv _ _ (lowRowsEquiv a c η hc θ d hd hs)
    (lowFromRow_energy a κ c η hc θ d hd hs)

end
end ElementaryPositivity.RawShuffle

end
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
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_HNTorusFactor
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic EnergyLaurent QuantumTorus WeightedTorusSeries WallUnits
open PowerSeries
noncomputable section
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0 < c i)
  [Fact (∀ θ,SlopeEulerSymmetric a c η θ)]
variable (w : I → ℕ) [Fact (∀i,0<w i)]
variable {M : Type*} [AddCommGroup M]
variable (Ω : M →+ M →+ ℤ) (P : (I → ℕ) →+ M)
variable (hΩ : ∀d e,Ω (P d) (P e)=eulerForm a d e-eulerForm a e d)

include hΩ in
lemma hnSeries_convolution (θ : ℝ) :
    hnSeries a κ c η hc=convolution LaurentRay.vUnit Ω P
      (highSeries a κ c η hc θ) (lowSeries a κ c η hc θ) := by
  funext d
  rw [hnSeries_threshold a κ c η hc θ]
  apply Finset.sum_congr rfl
  intro s hs
  rw [LaurentRay.vUnit_zpow,hΩ]

include hΩ in
theorem hnTorus_factorization (θ : ℝ) :
    push w LaurentRay.vUnit Ω P (hnSeries a κ c η hc)=
      push w LaurentRay.vUnit Ω P (highSeries a κ c η hc θ)*
      push w LaurentRay.vUnit Ω P (lowSeries a κ c η hc θ) := by
  rw [hnSeries_convolution a κ c η hc Ω P hΩ θ,push_convolution]

variable (h : M →+ ℝ) (θ : ℝ) (hh : ∀d,h (P d)=slopeValue c η θ d)

include hΩ hh in
theorem hnTorus_canonical_factors :
    push w LaurentRay.vUnit Ω P (highSeries a κ c η hc θ)=
        PowerSeriesSplit.leftFactor (positiveProject LaurentRay.vUnit Ω h)
          (push w LaurentRay.vUnit Ω P (hnSeries a κ c η hc)) ∧
    push w LaurentRay.vUnit Ω P (lowSeries a κ c η hc θ)=
        PowerSeriesSplit.rightFactor (positiveProject LaurentRay.vUnit Ω h)
          (push w LaurentRay.vUnit Ω P (hnSeries a κ c η hc)) := by
  apply PowerSeriesSplit.uniqueness
  · exact push_constant w _ _ _ _ (highSeries_zero a κ c η hc θ)
  · exact push_constant w _ _ _ _ (lowSeries_zero a κ c η hc θ)
  · exact (hnTorus_factorization a κ c η hc w Ω P hΩ θ).symm
  · exact project_push_fixed w _ _ _ h _ (fun d hd=>by
      rw [hh]
      exact highSeries_support a κ c η hc θ d hd)
  · intro n
    exact project_push_killed w _ _ _ h _ (fun d hd=>by
      rw [hh]
      exact lowSeries_support a κ c η hc θ d hd) (n+1)

end
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_HNZeroFactor
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic EnergyLaurent QuantumTorus WeightedTorusSeries WallUnits
open PowerSeries
noncomputable section
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0 < c i)
  [Fact (∀ θ,SlopeEulerSymmetric a c η θ)]

lemma zeroBlockCoefficient_eq (θ : ℝ) (d : I → ℕ) :
    zeroBlockCoefficient a κ c η hc θ d=
      if slopeValue c η θ d=0 then lowSeries a κ c η hc θ d else 0 := by
  classical
  unfold zeroBlockCoefficient
  by_cases hd : d=0
  · subst d
    simp only [dite_eq_left trivial,slopeValue_zero,ite_true, if_true,lowSeries_zero]
  · rw [dite_eq_right hd]
    by_cases hz : slopeValue c η θ d=0
    · rw [ite_eq_left hz,ite_eq_left hz]
      exact (lowSeries_on_slope a κ c η hc θ d hd
        ((slopeValue_eq_zero_iff c η hc θ d hd).mp hz)).symm
    · rw [ite_eq_right hz,ite_eq_right hz]

variable (w : I → ℕ) [Fact (∀i,0<w i)]
variable {M : Type*} [AddCommGroup M]
variable (Ω : M →+ M →+ ℤ) (P : (I → ℕ) →+ M)
variable (hΩ : ∀d e,Ω (P d) (P e)=eulerForm a d e-eulerForm a e d)
variable (h : M →+ ℝ) (θ : ℝ) (hh : ∀d,h (P d)=slopeValue c η θ d)

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.instAddCommMonoidTorusLaurentSeriesRatVUnit
include hh in
lemma zeroBlockCoeff_project (n : ℕ) :
    coeff n (push w LaurentRay.vUnit Ω P (zeroBlockCoefficient a κ c η hc θ))=
      zeroProject LaurentRay.vUnit Ω h (coeff n (push w LaurentRay.vUnit Ω P (lowSeries a κ c η hc θ))) := by
  classical
  simp only [push,coeff_mk,pushCoeff,map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [zeroProject_monomial,zeroBlockCoefficient_eq,hh]
  split_ifs <;> simp only [Torus.monomial_zero]

include hΩ hh in

theorem hnTorus_zeroFactor :
    push w LaurentRay.vUnit Ω P (zeroBlockCoefficient a κ c η hc θ)=
      PowerSeriesSplit.zeroFactor (positiveProject LaurentRay.vUnit Ω h)
        (zeroProject LaurentRay.vUnit Ω h) (push w LaurentRay.vUnit Ω P (hnSeries a κ c η hc)) := by
  apply PowerSeries.ext
  intro n
  rw [zeroFactor_coeff_projection,←(hnTorus_canonical_factors a κ c η hc w Ω P hΩ h θ hh).2]
  exact zeroBlockCoeff_project a κ c η hc w Ω P h θ hh n

include hΩ hh in
theorem literalInput_zeroFactor (ε : I → Bool) (ha : ∀i,a i i=elementaryDiagonal ε i) :
    push w LaurentRay.vUnit Ω P (zeroBlockCoefficient a κ c η hc θ)=
      PowerSeriesSplit.zeroFactor (positiveProject LaurentRay.vUnit Ω h)
        (zeroProject LaurentRay.vUnit Ω h) (push w LaurentRay.vUnit Ω P (literalInputCoefficient a κ ε)) := by
  have he : literalInputCoefficient a κ ε=hnSeries a κ c η hc :=
    funext (literalInput_hnSeries a κ c η hc ε ha)
  rw [he]
  exact hnTorus_zeroFactor a κ c η hc w Ω P hΩ h θ hh

end
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic SignedMultiplicity UnitSelections EnergyLaurent
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0 < c i)
  [hχ : Fact (∀θ,SlopeEulerSymmetric a c η θ)]

local instance instFactSlopeEulerSymmetric_1_rfdb662_1 (θ : ℝ) : Fact (SlopeEulerSymmetric a c η θ) := ⟨hχ.out θ⟩
lemma primitiveCountsSeries_vanish (θ : ℝ) (d : I → ℕ) (hd : ¬OnSlopeOrZero c η θ d) :
    primitiveCountsSeries a κ c η hc θ d=0 := by
  let : IsEmpty (PrimitiveCounts a c η hc θ d) :=
    ⟨fun x=>hd (primitiveCounts_onSlope a c η hc θ d x)⟩
  ext j
  rw [primitiveCountsSeries,series_coeff]
  simp

lemma primitiveCountsSeries_eq_zeroBlock (θ : ℝ) (d : I → ℕ) :
    primitiveCountsSeries a κ c η hc θ d=zeroBlockCoefficient a κ c η hc θ d := by
  by_cases hd : d=0
  · subst d
    rw [primitiveCountsSeries_zero]
    simp only [zeroBlockCoefficient,dite_eq_left trivial]
  · rw [zeroBlockCoefficient,dite_eq_right hd]
    by_cases hz : slopeValue c η θ d=0
    · rw [ite_eq_left hz]
      have hs := (slopeValue_eq_zero_iff c η hc θ d hd).mp hz
      subst θ
      exact series_equiv _ _ (primitiveCountsRows a c η hc d)
        (primitiveCountsRows_energy a κ c η hc d)
    · rw [ite_eq_right hz]
      apply primitiveCountsSeries_vanish
      intro H
      apply hz
      exact (slopeValue_eq_zero_iff c η hc θ d hd).mpr (H.resolve_left hd)

open QuantumTorus WeightedTorusSeries WallUnits
variable (w : I → ℕ) [Fact (∀i,0<w i)]
variable {M : Type*} [AddCommGroup M]
variable (Ω : M →+ M →+ ℤ) (P : (I → ℕ) →+ M)
variable (hΩ : ∀d e,Ω (P d) (P e)=eulerForm a d e-eulerForm a e d)
variable (h : M →+ ℝ) (θ : ℝ) (hh : ∀d,h (P d)=slopeValue c η θ d)

include hΩ hh in

theorem literalInput_primitiveFactor_oai (ε : I → Bool) (ha : ∀i,a i i=elementaryDiagonal ε i) :
    push w LaurentRay.vUnit Ω P (primitiveCountsSeries a κ c η hc θ)=
      PowerSeriesSplit.zeroFactor (positiveProject LaurentRay.vUnit Ω h)
        (zeroProject LaurentRay.vUnit Ω h)
        (push w LaurentRay.vUnit Ω P (literalInputCoefficient a κ ε)) := by
  rw [funext (primitiveCountsSeries_eq_zeroBlock a κ c η hc θ)]
  exact literalInput_zeroFactor a κ c η hc w Ω P hΩ h θ hh ε ha

end
end ElementaryPositivity.RawShuffle

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.ElementaryPositivity.RawShuffle.literalInput_primitiveFactor_oai.{u_1, u_2} := @OAI.ElementaryPositivity.RawShuffle.literalInput_primitiveFactor_oai.{u_1, u_2}
