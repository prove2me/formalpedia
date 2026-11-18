-- Prove2me | solution 1 for OAI.ElementaryPositivity.TriangularDynamics.admissible_polynomial_expansion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T20:19:27.015148+00:00
-- url     : https://prove2.me/submissions/fdc627a1-30f8-4e63-8dec-9af1981e8f33

import Mathlib
import Definitions.Def_ElementaryPositivity
import Definitions.Def_OAIQ368Chrom060
import Theorems.Thm_OAI_ElementaryPositivity_TriangularDynamics_historyWeight_positive

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_LaurentPolynomialEnergy
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LaurentPositive
open WallUnits
open scoped BigOperators
open Classical
noncomputable section

lemma qLaurent_monomial (k a:ℕ) : qLaurent (Polynomial.monomial k a)=HahnSeries.single (-2*(k:ℤ)) (a:ℚ) := by
  change Polynomial.eval₂ (Nat.castRingHom _) (HahnSeries.single (-2) 1) (Polynomial.monomial k a)=_
  rw [Polynomial.eval₂_monomial]
  change (a:LaurentSeries ℚ)*HahnSeries.single (-2) 1 ^ k=_
  rw [←HahnSeries.single_zero_natCast,HahnSeries.single_pow,HahnSeries.single_mul_single]
  simp [mul_comm]

lemma centered_zero (M:ℕ) : centered M 0=0:=by simp [centered]
lemma centered_add (M:ℕ) (p q:Polynomial ℕ) : centered M (p+q)=centered M p+centered M q:=by
  simp [centered,mul_add]
lemma centered_sum {A:Type*} [Fintype A] (M:ℕ) (p:A → Polynomial ℕ) :
    centered M (∑a,p a)=∑a,centered M (p a):=by simp [centered,Finset.mul_sum]
lemma centered_mul (M:ℕ) (p q:Polynomial ℕ) : centered M (p*q)=centered M p*qLaurent q:=by
  simp [centered,mul_assoc]
lemma centered_monomial (M k a:ℕ) :
    centered M (Polynomial.monomial k a)=HahnSeries.single ((M:ℤ)-2*(k:ℤ)) (a:ℚ) := by
  rw [centered,qLaurent_monomial,HahnSeries.single_mul_single,one_mul]
  congr 1
lemma centered_coeff (M:ℕ) (p:Polynomial ℕ) (k:ℕ) :
    (centered M p).coeff ((M:ℤ)-2*(k:ℤ))=(p.coeff k:ℚ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq=>rw [centered_add,HahnSeries.coeff_add,Polynomial.coeff_add,Nat.cast_add,hp,hq]
  | monomial e a=>
    rw [centered_monomial,HahnSeries.coeff_single,Polynomial.coeff_monomial]
    have he:((M:ℤ)-2*(k:ℤ)=(M:ℤ)-2*(e:ℤ)) ↔ e=k:=by omega
    simp only [he]
    split_ifs <;> simp
lemma centered_injective (M:ℕ) : Function.Injective (centered M) := by
  intro p q h
  ext k
  have H:=congrArg (fun w:LaurentSeries ℚ=>w.coeff ((M:ℤ)-2*(k:ℤ))) h
  rw [centered_coeff,centered_coeff] at H
  exact_mod_cast H
lemma centered_X_pow (M k:ℕ) :
    centered M (Polynomial.X^k)=(↑(LaurentRay.vUnit^(2*(k:ℤ)-(M:ℤ))):LaurentSeries ℚ) := by
  rw [←Polynomial.monomial_one_right_eq_X_pow,centered_monomial,LaurentRay.vUnit_zpow]
  congr 1
  ring_nf

lemma map_elementary_coeff {A B:Type*} [Fintype A] [Fintype B]
    (μ:A →₀ ℕ) (a:B →₀ ℕ) :
    qLaurent ((∏i:A,MvPolynomial.esymm B (Polynomial ℕ) (μ i)).coeff a)=
      (∏i:A,MvPolynomial.esymm B (LaurentSeries ℚ) (μ i)).coeff a := by
  rw [←MvPolynomial.coeff_map]
  simp only [map_prod,MvPolynomial.map_esymm]
end
end ElementaryPositivity.LaurentPositive

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Witness_ProfilePartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open Packets
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ} (G:NaturalUnitIntervalGraph n)

lemma admissibleHistoryEquiv_energy (w:{w:Equiv.Perm (Fin n) // G.Admissible w}) :
    leafEnergy G (admissibleHistoryEquiv G w)=G.graphInversions w.val:=
  (exactHistoryMatching G ∅).property (admissibleExactEquiv G w)

end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Witness_ElementaryProductDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.NaturalUnitIntervalGraph
open Packets
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ} (G:NaturalUnitIntervalGraph n)
lemma inversion_coefficient (r:ℕ) (a:Fin r →₀ ℕ) :
    (G.inversionChromatic r).coeff a=
    ∑κ:Fin n → Fin r,if G.Proper κ ∧ wordCount κ=a then
      (Polynomial.X^G.coloringInversions κ:Polynomial ℕ) else 0 := by
  unfold inversionChromatic
  rw [MvPolynomial.coeff_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro κ hκ
  by_cases hp:G.Proper κ
  · simp only [hp,ite_true, if_true,true_and,coloring_monomial,MvPolynomial.coeff_C_mul,MvPolynomial.coeff_monomial]
    split_ifs <;> simp
  · simp [hp]
lemma inversion_coefficient_zero (r:ℕ) (a:Fin r →₀ ℕ) (ha:a.degree≠n) :
    (G.inversionChromatic r).coeff a=0 := by
  rw [inversion_coefficient]
  apply Finset.sum_eq_zero
  intro κ hκ
  rw [ite_eq_right]
  rintro ⟨_,he⟩
  exact ha (he ▸ wordCount_degree κ)
end
end ElementaryPositivity.NaturalUnitIntervalGraph

end
section
namespace ElementaryPositivity.TriangularDynamics
open Packets WallUnits
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ} (G:NaturalUnitIntervalGraph n)

lemma decorated_polynomial_expansion (r:ℕ) : G.inversionChromatic r=
    ∑d:DecoratedLeaf G,MvPolynomial.C (Polynomial.X^leafEnergy G d)*
      MvPolynomial.esymmPart (Fin r) (Polynomial ℕ) (leafPartition G d) := by
  apply MvPolynomial.ext
  intro a
  simp only [MvPolynomial.coeff_sum,MvPolynomial.coeff_C_mul,leafPartition,esymmPart_profile]
  by_cases ha:a.degree=n
  · apply LaurentPositive.centered_injective G.edgeCount
    rw [G.inversion_coefficient,LaurentPositive.centered_sum,LaurentPositive.centered_sum]
    simp only [LaurentPositive.centered_mul,LaurentPositive.map_elementary_coeff,
      LaurentPositive.centered_X_pow]
    have he:∀κ:Fin n → Fin r, wordCount κ=a ↔ ∀c,(Finset.univ.filter (fun j=>κ j=c)).card=a c:=by
      intro κ
      constructor
      · intro h c; rw [←h,wordCount_apply]
      · intro h; ext c; rw [wordCount_apply]; exact h c
    simp only [apply_ite,LaurentPositive.centered_X_pow,LaurentPositive.centered_zero,he]
    exact decorated_coefficient G r a ha
  · rw [G.inversion_coefficient_zero r a ha]
    symm
    apply Finset.sum_eq_zero
    intro d hd
    rw [ElementaryMatrix.elementary_product_coeff_zero _ _ (by simpa only [historyProfile_degree] using ha),mul_zero]

lemma admissible_polynomial_expansion_oai (r:ℕ) : G.inversionChromatic r=
    ∑w:{w:Equiv.Perm (Fin n) // G.Admissible w},
      MvPolynomial.C (Polynomial.X^G.graphInversions w.val)*
        MvPolynomial.esymmPart (Fin r) (Polynomial ℕ) (admissiblePartition G w) := by
  rw [decorated_polynomial_expansion,←Equiv.sum_comp (admissibleHistoryEquiv G)]
  apply Finset.sum_congr rfl
  intro w hw
  rw [admissibleHistoryEquiv_energy]
  rfl
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

theorem solution : type_of% @OAI.ElementaryPositivity.TriangularDynamics.admissible_polynomial_expansion_oai := @OAI.ElementaryPositivity.TriangularDynamics.admissible_polynomial_expansion_oai
