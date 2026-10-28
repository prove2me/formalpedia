-- Prove2me | solution 1 for OAI.Lech.cyclicDuttaSequence_small
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:17:09.079807+00:00
-- url     : https://prove2.me/submissions/8e21b031-d54b-49eb-94cd-b5e4a92a1a0b

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L014
import Definitions.Def_OAIQ032L018
import Theorems.Thm_OAI_Lech_frobenius_quotient_homology_tendsto_zero

section
-- module Solutions.OAIQ032_LECH.Multiplicity_SubalgebraStageFromBase
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors

open scoped nonZeroDivisors


namespace Lech



theorem dimension_cast (A : Type*) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] : (dimension A : WithBot ℕ∞) = ringKrullDim A := by
  have hb := ringKrullDim_ne_bot (R := A)
  have ht := ringKrullDim_ne_top (R := A)
  unfold dimension
  generalize he : ringKrullDim A = d at *
  cases d with
  | bot => exact (hb rfl).elim
  | coe d =>
    simp only [WithBot.unbotD_coe]
    exact congrArg (fun x : ℕ∞ => (x : WithBot ℕ∞))
      (ENat.natCast_toNat (fun h => ht (by simp [h])))



end Lech
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PowerSeriesFinDimension
attribute [-instance] _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
open scoped Classical Pointwise
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
open scoped ENNReal ZeroObject
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open CategoryTheory


namespace Lech.Normalization
open IsLocalRing
variable (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

 
lemma exists_parameters : ∃ (n : ℕ) (z : Fin n → R),
    (∀ i, z i ∈ maximalIdeal R) ∧
    (Ideal.span (Set.range z)).radical = maximalIdeal R ∧
    ringKrullDim R = n := by
  classical
  obtain ⟨s,hs,hcard⟩ := (maximalIdeal R).exists_finset_card_eq_height_of_isNoetherianRing
  let e := s.equivFin
  let z : Fin s.card → R := fun i => (e.symm i : R)
  have hrange : Set.range z = (s : Set R) := by
    ext r
    constructor
    · rintro ⟨i,rfl⟩
      exact (e.symm i).2
    · intro hr
      exact ⟨e ⟨r,hr⟩,by simp [z]⟩
  refine ⟨s.card,z,?_,?_,?_⟩
  · intro i
    exact hs.le (Ideal.subset_span (by rw [← hrange]; exact Set.mem_range_self i))
  · rw [hrange,← Ideal.sInf_minimalPrimes]
    apply le_antisymm (sInf_le hs)
    apply le_sInf
    intro Q hQ
    let : Q.IsPrime := hQ.isPrime
    exact hs.2 hQ.1 (le_maximalIdeal_of_isPrime Q)
  · rw [← maximalIdeal_height_eq_ringKrullDim,← hcard]
    rfl
end Lech.Normalization


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_DuttaEulerLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter
open scoped Topology
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
lemma frobenius_weight_eq (p d n : ℕ) :
    (p:ℝ)^(-(n*d:ℤ)) = (((p:ℝ)^n)^d)⁻¹ := by
  rw [← Nat.cast_mul,zpow_neg,zpow_natCast,pow_mul]

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PrimeQuotientParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open IsLocalRing
open scoped nonZeroDivisors
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

lemma exists_prime_quotient_parameters (I : Ideal R) [I.IsPrime]
    (hsmall : dimension (R ⧸ I) < dimension R) :
    ∃ zs : List R, zs.length < dimension R ∧
      (∀ z∈zs,z∈maximalIdeal R) ∧
      (I ⊔ Koszul.entryIdeal zs).radical = maximalIdeal R := by
  classical
  let Q := R ⧸ I
  let f : R →+* Q := Ideal.Quotient.mk I
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  have : IsLocalRing Q := IsLocalRing.of_surjective' f hf
  have : IsLocalHom f := IsLocalHom.of_surjective f hf
  obtain ⟨n,y,hy,hrad,hdim⟩ := Normalization.exists_parameters Q
  choose z hz using fun i => hf (y i)
  have hlen : n < dimension R := by
    have hn : dimension Q = n := by
      have h := dimension_cast Q
      rw [hdim] at h
      exact_mod_cast h
    change dimension Q < dimension R at hsmall
    simpa only [hn] using hsmall
  have hm : ∀ i,z i ∈ maximalIdeal R := by
    intro i
    change ¬ IsUnit (z i)
    intro hu
    have hc : IsUnit (y i) := hz i ▸ hu.map f
    exact hy i hc
  refine ⟨List.ofFn z,by simpa,?_,?_⟩
  · intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact hm i
  · have hmap : (I ⊔ Koszul.entryIdeal (List.ofFn z)).map f = Ideal.span (Set.range y) := by
      simp only [Ideal.map_sup,Koszul.entryIdeal,Ideal.map_span]
      have he : f '' {x | x ∈ List.ofFn z} = Set.range y := by
        ext x
        simp only [Set.mem_image,List.mem_ofFn,Set.mem_ofPred_eq,Set.mem_range]
        constructor
        · rintro ⟨a,⟨i,rfl⟩,rfl⟩
          exact ⟨i,(hz i).symm⟩
        · rintro ⟨i,rfl⟩
          exact ⟨z i,⟨i,rfl⟩,hz i⟩
      rw [he,Ideal.map_quotient_self,bot_sup_eq]
    have hrad' : ((I ⊔ Koszul.entryIdeal (List.ofFn z)).map f).radical = maximalIdeal Q :=
      hmap ▸ hrad
    have hcom := congrArg (Ideal.comap f) hrad'
    rw [Ideal.comap_radical,Ideal.comap_map_of_surjective f hf] at hcom
    have hmQ : Ideal.comap f (maximalIdeal Q) = maximalIdeal R := by
      ext x
      change (¬ IsUnit (f x)) ↔ ¬ IsUnit x
      exact not_congr (isUnit_map_iff f x)
    rw [hmQ] at hcom
    rw [← RingHom.ker_eq_comap_bot,Ideal.mk_ker] at hcom
    change ((I ⊔ Koszul.entryIdeal (List.ofFn z)) ⊔ I).radical = maximalIdeal R at hcom
    rw [sup_eq_left.mpr (show I≤I⊔Koszul.entryIdeal (List.ofFn z) from le_sup_left)] at hcom
    exact hcom
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CyclicDutta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter IsLocalRing
open scoped Topology TensorProduct
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
attribute [local instance] quotient_local quotient_localHom

lemma cyclicDuttaSequence_small_oai (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsFiniteHomologyComplex R F)
    (P : Ideal R) [P.IsPrime] (hd : dimension (R ⧸ P)<dimension R) :
    Tendsto (cyclicDuttaSequence p F P) atTop (𝓝 0) := by
  obtain ⟨zs,hlen,hzs,hprim⟩ := exists_prime_quotient_parameters P hd
  have hi (i : ℕ) := (frobenius_quotient_homology_tendsto_zero p F hF P zs hzs hprim hlen
    (-(i:ℤ))).const_mul ((-1:ℝ)^i)
  have hsum := tendsto_finsetSum (Finset.range (dimension R+1)) (fun i _ => hi i)
  simp only [mul_zero,Finset.sum_const_zero] at hsum
  apply hsum.congr
  intro n
  unfold cyclicDuttaSequence shortEuler
  rw [frobenius_weight_eq,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have e := (NatIso.mapHomologicalComplex (TensorTotal.termTensorQuotientIso P) (.up ℤ)).app
    (frobeniusComplex R p n F)
  have he := (homologyMapIso e (-(i:ℤ))).toLinearEquiv.length_eq
  change Module.length R (((tensorModuleFunctor (frobeniusComplex R p n F)).obj
    (ModuleCat.of R (R ⧸ P))).homology (-(i:ℤ)))=_ at he
  rw [he,div_eq_mul_inv]
  unfold complexQuotient
  ring

end Lech

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.cyclicDuttaSequence_small_oai.{u} := @OAI.Lech.cyclicDuttaSequence_small_oai.{u}
