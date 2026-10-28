-- Prove2me | solution 1 for OAI.Lech.FrobeniusIntermediate.frobenius_homology_order_transfer
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:01:11.524018+00:00
-- url     : https://prove2.me/submissions/e4c306d2-d46b-49e4-8ed8-dda3341e6e0b

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L014
import Theorems.Thm_OAI_Lech_exists_scalar_extension_homology_bound
import Theorems.Thm_OAI_Lech_finiteHomology_extendScalars
import Theorems.Thm_OAI_Lech_frobenius_quotient_homology_finiteLength
import Theorems.Thm_OAI_Lech_frobenius_quotient_homology_tendsto_zero
import Theorems.Thm_OAI_Lech_frobenius_shortComplex_homology_finiteLength

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
-- module Solutions.OAIQ032_LECH.Multiplicity_LechLengthLe
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

open scoped BigOperators


namespace Lech.FrobeniusGrowth
open scoped nonZeroDivisors
variable {R : Type*} [CommRing R]


variable [IsNoetherianRing R] [IsLocalRing R]

lemma quotient_dimension_lt {g : R} (hg : g ∈ R⁰) [IsLocalRing (R ⧸ Ideal.span {g})] :
    Lech.dimension (R ⧸ Ideal.span {g}) < Lech.dimension R := by
  have hh := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hg
  rw [← Lech.dimension_cast (R ⧸ Ideal.span {g}),← Lech.dimension_cast R] at hh
  have hh' : (Lech.dimension (R ⧸ Ideal.span {g}) : WithBot ℕ∞) +
      (1 : WithBot ℕ∞) ≤ (Lech.dimension R : WithBot ℕ∞) := hh
  exact_mod_cast hh'

open Filter
open scoped Topology


end Lech.FrobeniusGrowth


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusIntermediatePowerMap
attribute [-instance] _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
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
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
namespace Lech.FrobeniusIntermediate
variable {D : Type*} [CommRing D] (p : ℕ) [Fact p.Prime] [CharP D p]
    (B : Subring D) (e : ℕ) (he : ∀ x : D, x^(p^e) ∈ B)

lemma powerMap_val (x : D) : (powerMap p B e he x : D) = x^(p^e) := rfl

lemma map_radical_primary [IsLocalRing D] [IsLocalRing B] [IsLocalHom B.subtype]
    (H : Ideal D) (hH : H.radical = IsLocalRing.maximalIdeal D) :
    (H.map (powerMap p B e he)).radical = IsLocalRing.maximalIdeal B := by
  apply le_antisymm
  · apply (IsLocalRing.maximalIdeal.isMaximal B).isPrime.isRadical.radical_le_iff.mpr
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    exact IsLocalRing.mem_maximalIdeal (powerMap p B e he x) |>.mpr
      (fun hunit => (IsLocalRing.mem_maximalIdeal x).mp
        (hH ▸ Ideal.le_radical hx) (isUnit_of_map_unit (powerMap p B e he) _ hunit))
  · intro b hb
    have hd : (b : D) ∈ H.radical := by
      rw [hH]
      exact show (b : D) ∈ IsLocalRing.maximalIdeal D from
        (show b ∈ (IsLocalRing.maximalIdeal D).comap B.subtype from
          (IsLocalRing.maximalIdeal_comap B.subtype).symm ▸ hb)
    obtain ⟨n,hn⟩ := hd
    refine ⟨n*(p^e),?_⟩
    have hg := Ideal.mem_map_of_mem (powerMap p B e he) hn
    convert hg using 1
    all_goals try with_reducible_and_instances rfl
    apply Subtype.ext
    simp only [powerMap_val,Subring.coe_pow,pow_mul]

end Lech.FrobeniusIntermediate


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
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusHomologyGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open scoped TensorProduct
namespace Lech
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

lemma free_extendScalars (φ : R →+* S) (M : ModuleCat.{u} R) [Module.Free R M] :
    Module.Free S ((ModuleCat.extendScalars φ).obj M) := by
  let := φ.toAlgebra
  change Module.Free S (S ⊗[R] M)
  infer_instance

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_QuotientParameters
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

lemma exists_small_quotient_parameters (g : R) (hg : g∈R⁰) (hu : ¬IsUnit g) :
    ∃ zs : List R, zs.length < dimension R ∧
      (∀ z∈zs,z∈maximalIdeal R) ∧
      (Ideal.span {g} ⊔ Koszul.entryIdeal zs).radical = maximalIdeal R := by
  classical
  let I : Ideal R := Ideal.span {g}
  have hI : I ≠ ⊤ := fun h => hu (Ideal.span_singleton_eq_top.mp h)
  let Q := R ⧸ I
  let f : R →+* Q := Ideal.Quotient.mk I
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  have : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hI
  have : IsLocalRing Q := IsLocalRing.of_surjective' f hf
  have : IsLocalHom f := IsLocalHom.of_surjective f hf
  obtain ⟨n,y,hy,hrad,hdim⟩ := Normalization.exists_parameters Q
  choose z hz using fun i => hf (y i)
  have hlen : n < dimension R := by
    have hn : dimension Q = n := by
      have h := dimension_cast Q
      rw [hdim] at h
      exact_mod_cast h
    have ht : dimension Q < dimension R := FrobeniusGrowth.quotient_dimension_lt hg
    simpa only [hn] using ht
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
-- module Solutions.OAIQ032_LECH.Multiplicity_ScalarQuotientTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace Lech
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

lemma free_scalar_injective [IsDomain R] (M : ModuleCat.{u} R) [Module.Free R M]
    (g : R) (hg : g ≠ 0) : Function.Injective (fun x : M => g • x) :=
  smul_right_injective M hg
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusScalarError
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
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
lemma frobenius_scalar_quotient_homology_tendsto_zero
    (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsFiniteHomologyComplex R F)
    (g : R) (hg : g ≠ 0) (i : ℤ) :
    Tendsto (fun n : ℕ => ((Module.length R (((complexQuotient (Ideal.span {g}) (.up ℤ)).obj
      (frobeniusComplex R p n F)).homology i)).toNat : ℝ) / ((p:ℝ)^n)^(dimension R)) atTop (𝓝 0) := by
  by_cases hu : IsUnit g
  · have hz (n : ℕ) : Module.length R (((complexQuotient (Ideal.span {g}) (.up ℤ)).obj
        (frobeniusComplex R p n F)).homology i) = 0 := by
      let Q := (complexQuotient (Ideal.span {g}) (.up ℤ)).obj (frobeniusComplex R p n F)
      have he : g • 𝟙 Q = 0 := complexQuotient_annihilated (Ideal.span {g}) g
        (Ideal.subset_span (Set.mem_singleton g)) (frobeniusComplex R p n F)
      have hQ : IsZero Q := (IsZero.iff_id_eq_zero Q).mpr (hu.smul_eq_zero.mp he)
      have : Subsingleton (Q.homology i) := ModuleCat.isZero_iff_subsingleton.mp
        ((homologyFunctor (ModuleCat R) (.up ℤ) i).map_isZero hQ)
      exact Module.length_eq_zero (R:=R) (M:=Q.homology i)
    simpa only [hz,ENat.toNat_zero,Nat.cast_zero,zero_div] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
  · obtain ⟨zs,hd,hzs,hprim⟩ := exists_small_quotient_parameters g
      (mem_nonZeroDivisors_of_ne_zero hg) hu
    exact frobenius_quotient_homology_tendsto_zero p F hF (Ideal.span {g}) zs hzs hprim hd i

lemma tendsto_frobenius_shift_zero (p d e : ℕ) (hp : 0 < p) (a : ℕ → ℝ)
    (ha : Tendsto (fun n => a n / ((p:ℝ)^n)^d) atTop (𝓝 0)) :
    Tendsto (fun n => a (e+n) / ((p:ℝ)^n)^d) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => e+n) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat e
  have ht := ha.comp hn
  have hc := ht.const_mul (((p:ℝ)^e)^d)
  simp only [mul_zero] at hc
  apply hc.congr
  intro n
  dsimp only [Function.comp_apply]
  rw [pow_add,mul_pow]
  have h0 : ((p:ℝ)^e)^d ≠ 0 := by positivity
  rw [← mul_div_assoc]
  exact mul_div_mul_left _ _ h0

lemma tendsto_frobenius_unshift_zero (p d e : ℕ) (_hp : 0 < p) (a : ℕ → ℝ)
    (ha : Tendsto (fun n => a (e+n) / ((p:ℝ)^n)^d) atTop (𝓝 0)) :
    Tendsto (fun n => a n / ((p:ℝ)^n)^d) atTop (𝓝 0) := by
  apply (tendsto_add_atTop_iff_nat e).mp
  have ht := ha.div_const (((p:ℝ)^e)^d)
  simp only [zero_div] at ht
  apply ht.congr
  intro n
  rw [Nat.add_comm n e,pow_add,mul_pow]
  ring
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RobertsOrderTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter
open scoped Topology
namespace Lech.FrobeniusIntermediate
universe u
variable {D : Type u} [CommRing D] [IsDomain D] [IsNoetherianRing D] [IsLocalRing D]
  (p : ℕ) [Fact p.Prime] [CharP D p]
  (B : Subring D) [IsLocalRing B] [IsNoetherianRing B] [IsLocalHom B.subtype]
  [Module.Finite B D]



theorem frobenius_homology_order_transfer_oai
    (e : ℕ) (he : ∀ x : D,x^(p^e) ∈ B)
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField D)))
    (hd : dimension B = dimension D)
    (F : CochainComplex (ModuleCat.{u} D) ℤ) (hF : IsFiniteHomologyComplex D F)
    (i : ℤ)
    (hlim : Tendsto (fun n : ℕ => ((Module.length B ((frobeniusComplex B p n
      (((ModuleCat.extendScalars (powerMap p B e he)).mapHomologicalComplex _).obj F)).homology i)).toNat : ℝ) /
        ((p:ℝ)^n)^(dimension B)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ((Module.length D ((frobeniusComplex D p n F).homology i)).toNat : ℝ) /
      ((p:ℝ)^n)^(dimension D)) atTop (𝓝 0) := by
  have hp0 : 0 < (p:ℝ) := by exact_mod_cast (Nat.Prime.pos (Fact.out : p.Prime))
  let G := ((ModuleCat.extendScalars (powerMap p B e he)).mapHomologicalComplex (.up ℤ)).obj F
  obtain ⟨r,g,hg,hbound⟩ := exists_scalar_extension_homology_bound (R:=B) (S:=D) hres
  have hgD : (g:D) ≠ 0 := fun h => hg (Subtype.val_injective h)
  let a : D := g
  have hb (n : ℕ) : Module.length D ((frobeniusComplex D p (e+n) F).homology i) ≤
      r • Module.length B ((frobeniusComplex B p n G).homology i) +
      Module.length D (((complexQuotient (Ideal.span {a}) (.up ℤ)).obj
        (frobeniusComplex D p (e+n) F)).homology i) := by
    let U := ((ModuleCat.extendScalars B.subtype).mapHomologicalComplex (.up ℤ)).obj
      (frobeniusComplex B p n G)
    let iso := frobeniusComplex_order_iso p B e he F n
    have hfree (j : ℤ) : Module.Free D ((frobeniusComplex D p (e+n) F).X j) := by
      have := hF.term_free j
      exact free_extendScalars (iterateFrobenius D p (e+n)) (F.X j)
    have hgi (j : ℤ) : Function.Injective (fun x : U.X j => (algebraMap B D g) • x) := by
      let q := ((eval (ModuleCat D) (.up ℤ) j).mapIso iso).toLinearEquiv
      have := hfree j
      intro x y hxy
      apply q.injective
      apply free_scalar_injective ((frobeniusComplex D p (e+n) F).X j) a hgD
      exact (q.map_smul a x).symm.trans ((congrArg q hxy).trans (q.map_smul a y))
    have hlen : Module.length D (U.homology i) = Module.length D ((frobeniusComplex D p (e+n) F).homology i) :=
      (homologyMapIso iso i).toLinearEquiv.length_eq
    have hh := hbound (frobeniusComplex B p n G) i hgi (by
      change Module.length D (U.homology i) ≠ ⊤
      rw [hlen]
      exact Module.length_ne_top_iff.mpr (frobenius_shortComplex_homology_finiteLength p F hF (e+n) i))
    change Module.length D (U.homology i) ≤ _ at hh
    rw [hlen] at hh
    have hq : Module.length D (((complexQuotient (Ideal.span {a}) (.up ℤ)).obj U).homology i) =
        Module.length D (((complexQuotient (Ideal.span {a}) (.up ℤ)).obj (frobeniusComplex D p (e+n) F)).homology i) :=
      (homologyMapIso ((complexQuotient (Ideal.span {a}) (.up ℤ)).mapIso iso) i).toLinearEquiv.length_eq
    change Module.length D ((frobeniusComplex D p (e+n) F).homology i) ≤
      r • Module.length B ((frobeniusComplex B p n G).homology i) +
      Module.length D (((complexQuotient (Ideal.span {a}) (.up ℤ)).obj U).homology i) at hh
    rw [hq] at hh
    exact hh
  have hlim' : Tendsto (fun n : ℕ => (r:ℝ) *
      (((Module.length B ((frobeniusComplex B p n G).homology i)).toNat : ℝ) /
        ((p:ℝ)^n)^(dimension D))) atTop (𝓝 0) := by
    simpa only [hd,mul_zero] using hlim.const_mul (r:ℝ)
  have herr := tendsto_frobenius_shift_zero p (dimension D) e (Nat.Prime.pos Fact.out)
    (fun n => ((Module.length D (((complexQuotient (Ideal.span {a}) (.up ℤ)).obj
      (frobeniusComplex D p n F)).homology i)).toNat : ℝ))
    (frobenius_scalar_quotient_homology_tendsto_zero p F hF a hgD i)
  apply tendsto_frobenius_unshift_zero p (dimension D) e (Nat.Prime.pos Fact.out)
  apply squeeze_zero (g := fun n : ℕ =>
    (r:ℝ) * (((Module.length B ((frobeniusComplex B p n G).homology i)).toNat : ℝ) /
      ((p:ℝ)^n)^(dimension D)) +
    (((Module.length D (((complexQuotient (Ideal.span {a}) (.up ℤ)).obj
      (frobeniusComplex D p (e+n) F)).homology i)).toNat : ℝ) / ((p:ℝ)^n)^(dimension D)))
  · intro n; positivity
  · intro n
    rw [← mul_div_assoc,← add_div]
    apply (div_le_div_iff_of_pos_right (by positivity)).mpr
    have hG : IsFiniteHomologyComplex B G :=
      finiteHomology_extendScalars (powerMap p B e he) hd
        (map_radical_primary p B e he (IsLocalRing.maximalIdeal D) (Ideal.IsPrime.radical inferInstance)) F hF
    have hfinB := Module.length_ne_top_iff.mpr (frobenius_shortComplex_homology_finiteLength p G hG n i)
    have hfinQ := Module.length_ne_top_iff.mpr (frobenius_quotient_homology_finiteLength p F hF (Ideal.span {a}) (e+n) i)
    have hfinD := Module.length_ne_top_iff.mpr (frobenius_shortComplex_homology_finiteLength p F hF (e+n) i)
    have hh := hb n
    rw [← ENat.natCast_toNat hfinD,← ENat.natCast_toNat hfinB,← ENat.natCast_toNat hfinQ,nsmul_eq_mul] at hh
    exact_mod_cast hh

  · simpa only [add_zero] using hlim'.add herr
end Lech.FrobeniusIntermediate

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.FrobeniusIntermediate.frobenius_homology_order_transfer_oai.{u} := @OAI.Lech.FrobeniusIntermediate.frobenius_homology_order_transfer_oai.{u}
