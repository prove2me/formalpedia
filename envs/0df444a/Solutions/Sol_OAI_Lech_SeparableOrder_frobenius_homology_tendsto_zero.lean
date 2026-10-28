-- Prove2me | solution 1 for OAI.Lech.SeparableOrder.frobenius_homology_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:03:07.208106+00:00
-- url     : https://prove2.me/submissions/ad81d872-ab32-46d0-b7cc-36303d65ffe0

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L008
import Definitions.Def_OAIQ032L014
import Theorems.Thm_OAI_Lech_FrobeniusIntermediate_frobenius_homology_order_transfer
import Theorems.Thm_OAI_Lech_PerfectDomainStages_frobenius_homology_conductor_bound
import Theorems.Thm_OAI_Lech_finiteHomology_extendScalars
import Theorems.Thm_OAI_Lech_frobenius_quotient_homology_finiteLength
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


namespace Lech.PowerSeries
open MvPowerSeries
variable {σ R : Type*} [Fintype σ] [CommRing R]

lemma pick_zero : pick (0 : σ →₀ ℕ) = none := by simp [pick]
lemma pick_positive {d : σ →₀ ℕ} {i : σ} (hi : pick d = some i) : 0 < d i := by
  classical
  by_cases hd : d = 0
  · subst d; simp [pick] at hi
  · have hc : Classical.choose (exists_positive hd) = i := by
      exact Option.some.inj (by simpa only [pick,dite_eq_right hd] using hi)
    rw [← hc]
    exact Classical.choose_spec (exists_positive hd)

lemma exists_pick {d : σ →₀ ℕ} (hd : d ≠ 0) : ∃ i, pick d = some i := by
  simp [pick,hd]

lemma coeff_divide_X (f : MvPowerSeries σ R) (i : σ) (d : σ →₀ ℕ) :
    coeff d (divide f i * X i) = if pick d = some i then coeff d f else 0 := by
  classical
  rw [X,coeff_mul_monomial]
  by_cases hle : Finsupp.single i 1 ≤ d
  · rw [ite_eq_left hle]
    simp only [mul_one]
    change (if pick (d - Finsupp.single i 1 + Finsupp.single i 1) = some i then
      coeff (d - Finsupp.single i 1 + Finsupp.single i 1) f else 0) = _
    rw [tsub_add_cancel_of_le hle]
  · rw [ite_eq_right hle]
    have hp : pick d ≠ some i := by
      intro hc
      apply hle
      intro j
      by_cases hji : j = i
      · subst j; simpa using (Nat.succ_le_iff.mpr (pick_positive hc))
      · simp [hji]
    simp [hp]

 

lemma sum_divide_X (f : MvPowerSeries σ R) :
    ∑ i, divide f i * X i = f - C (constantCoeff f) := by
  classical
  ext d
  simp only [map_sum,coeff_divide_X,map_sub]
  by_cases hd : d = 0
  · subst d
    simp [pick_zero]
  · obtain ⟨i,hi⟩ := exists_pick hd
    rw [Finset.sum_eq_single i]
    · simp [hi,coeff_C,hd]
    · intro j _ hji
      simp [hi,Ne.symm hji]
    · simp

lemma variables_eq_ker_constantCoeff :
    Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) = RingHom.ker constantCoeff := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i,rfl⟩
    simp
  · intro f hf
    have hc : constantCoeff f = 0 := hf
    have h := sum_divide_X f
    rw [hc,map_zero,sub_zero] at h
    rw [← h]
    exact Ideal.sum_mem _ (fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i)))

variable {k : Type*} [Field k]
lemma maximalIdeal_eq_variables :
    IsLocalRing.maximalIdeal (MvPowerSeries σ k) =
      Ideal.span (Set.range (X : σ → MvPowerSeries σ k)) := by
  rw [variables_eq_ker_constantCoeff]
  ext f
  simp only [IsLocalRing.mem_maximalIdeal,RingHom.mem_ker,mem_nonunits_iff,isUnit_iff_constantCoeff,
    isUnit_iff_ne_zero,not_not]

end Lech.PowerSeries


namespace Lech.PowerSeries
open MvPowerSeries
variable (σ k : Type*) [Fintype σ] [Field k]

lemma dimension_le_variables : ringKrullDim (MvPowerSeries σ k) ≤ Fintype.card σ := by
  refine (ringKrullDim_le_spanFinrank_maximalIdeal _).trans ?_
  rw [maximalIdeal_eq_variables]
  have h := Submodule.spanFinrank_span_le_ncard_of_finite
    (R := MvPowerSeries σ k) (Set.finite_range (X : σ → MvPowerSeries σ k))
  have hcard : (Set.range (X : σ → MvPowerSeries σ k)).ncard ≤ Fintype.card σ := by
    rw [← Set.image_univ]
    exact (Set.ncard_image_le (Set.finite_univ)).trans (by simp)
  exact_mod_cast h.trans hcard

end Lech.PowerSeries


namespace Lech.PowerSeries
open MvPowerSeries
open scoped nonZeroDivisors
variable (k : Type*) [Field k]

lemma fin_le_dimension (h : ℕ) : (h : WithBot ℕ∞) ≤ ringKrullDim (MvPowerSeries (Fin h) k) := by
  induction h with
  | zero => exact Order.krullDim_nonneg
  | succ h ih =>
    let e : Fin h ↪ Fin (h+1) := Fin.succEmb h
    let f := (killCompl (R := k) e).toRingHom
    have hf : Function.Surjective f := fun x => ⟨rename e x,killCompl_rename_app x⟩
    have hx : (X 0 : MvPowerSeries (Fin (h+1)) k) ∈ (MvPowerSeries (Fin (h+1)) k)⁰ :=
      mem_nonZeroDivisors_iff_ne_zero.mpr (by
        intro hz
        have hc := congrArg (coeff (Finsupp.single 0 1)) hz
        simp at hc)
    have hz : f (X 0) = 0 := by
      apply killCompl_X_eq_zero
      rintro ⟨i,hi⟩
      exact Fin.succ_ne_zero i hi
    have hb := ringKrullDim_succ_le_of_surjective f hf hx hz
    calc
      (↑(h+1) : WithBot ℕ∞) = (h : WithBot ℕ∞) + 1 := by simp
      _ ≤ ringKrullDim (MvPowerSeries (Fin h) k) + 1 := add_le_add ih le_rfl
      _ ≤ _ := hb

lemma fin_dimension (h : ℕ) : ringKrullDim (MvPowerSeries (Fin h) k) = h := by
  apply le_antisymm _ (fin_le_dimension k h)
  simpa using dimension_le_variables (Fin h) k

end Lech.PowerSeries


namespace Lech
variable {R S : Type*} [CommRing R] [CommRing S]
lemma ringKrullDim_eq_of_integral_injective (f : R →+* S)
    (hint : f.IsIntegral) (hf : Function.Injective f) : ringKrullDim S = ringKrullDim R := by
  let : Algebra R S := f.toAlgebra
  let : Algebra.IsIntegral R S := ⟨hint⟩
  apply le_antisymm
  · apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap f)
    intro p q hpq
    exact Ideal.IsIntegral.comap_lt_comap hpq
  · apply iSup_le
    intro l
    obtain ⟨P,_,hP,hPP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral l.head.asIdeal (⊥ : Ideal S)
      (by rw [← RingHom.ker_eq_comap_bot]
          change RingHom.ker f ≤ _
          rw [(RingHom.injective_iff_ker_eq_bot f).mp hf]
          exact bot_le)
    have : P.LiesOver l.head.asIdeal := (Ideal.liesOver_iff _ _).mpr hPP.symm
    obtain ⟨L,hL,_,_⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
    simpa only [hL,ringKrullDim] using Order.LTSeries.length_le_krullDim L
end Lech


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


namespace Lech.SeparableOrder
variable (A D K L : Type*) [CommRing A] [CommRing D] [IsDomain D]
  [Field K] [Field L] [Algebra A D] [Algebra A K] [Algebra A L]
  [Algebra K L] [Algebra D L] [IsScalarTower A K L] [IsScalarTower A D L]



omit [IsDomain D] in
lemma toField_injective [IsFractionRing D L] : Function.Injective (toField A D K L) := by
  intro x y h
  apply Subtype.ext
  exact IsFractionRing.injective D L (congrArg Subtype.val h)

instance orderFieldFaithful [IsFractionRing D L] :
    FaithfulSMul (order A D K L) (separableClosure K L) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (toField_injective A D K L)

 
lemma order_inherits_units [IsFractionRing D L] {x : D} (hx : x ∈ order A D K L)
    (hu : IsUnit x) : IsUnit (⟨x,hx⟩ : order A D K L) := by
  obtain ⟨u,rfl⟩ := hu
  have hm : (↑(u⁻¹) : D) ∈ order A D K L := by
    change IsSeparable K (algebraMap D L (↑(u⁻¹) : D))
    have hi : algebraMap D L (↑(u⁻¹) : D) = (algebraMap D L (↑u : D))⁻¹ := by
      apply mul_left_cancel₀ (show algebraMap D L (↑u : D) ≠ 0 from
        (map_ne_zero_iff (algebraMap D L) (IsFractionRing.injective D L)).mpr (Units.ne_zero u))
      rw [← map_mul, Units.mul_inv, map_one, mul_inv_cancel₀]
      exact (map_ne_zero_iff (algebraMap D L) (IsFractionRing.injective D L)).mpr (Units.ne_zero u)
    rw [hi]
    exact Field.isSeparable_inv hx
  exact ⟨⟨⟨↑u,hx⟩,⟨↑(u⁻¹),hm⟩,by ext; exact Units.mul_inv u,
      by ext; exact Units.inv_mul u⟩,rfl⟩

instance orderLocal [IsFractionRing D L] [IsLocalRing D] :
    IsLocalRing (order A D K L) :=
  (order A D K L).toSubring.isLocalRing_of_unit (fun _ hx hu =>
    order_inherits_units A D K L hx hu)

instance orderInclusionLocal [IsFractionRing D L] [IsLocalRing D] :
    IsLocalHom (algebraMap (order A D K L) D) :=
  ⟨fun x hu => order_inherits_units A D K L x.2 hu⟩

variable (p : ℕ) [Fact p.Prime] [CharP K p] [CharP L p] [FiniteDimensional K L]

omit [IsDomain D] in
 

lemma uniform_power : ∃ n : ℕ, ∀ x : D, x^(p^n) ∈ order A D K L := by
  let E := separableClosure K L
  let : FiniteDimensional E L := FiniteDimensional.right K E L
  let : IsPurelyInseparable E L := separableClosure.isPurelyInseparable K L
  let : CharP E p := (Algebra.charP_iff K E p).mp inferInstance
  refine ⟨IsPurelyInseparable.exponent E L,fun x => ?_⟩
  change IsSeparable K (algebraMap D L (x^_))
  rw [map_pow]
  obtain ⟨y,hy⟩ := IsPurelyInseparable.exponent_def' E p (algebraMap D L x)
  rw [← hy]
  exact y.2

 

instance orderFraction [IsFractionRing D L] :
    IsFractionRing (order A D K L) (separableClosure K L) := by
  obtain ⟨n,hn⟩ := uniform_power A D K L p
  have hq : 0 < p^n := pow_pos (Nat.Prime.pos (Fact.out : p.Prime)) n
  apply IsFractionRing.of_field
  intro z
  obtain ⟨a,b,hb,hab⟩ := IsFractionRing.div_surjective D (z : L)
  have hb0 : algebraMap D L b ≠ 0 :=
    (map_ne_zero_iff (algebraMap D L) (IsFractionRing.injective D L)).mpr
      (nonZeroDivisors.coe_ne_zero ⟨b,hb⟩)
  have hid : algebraMap D L (a*b^(p^n-1)) = (z : L) * algebraMap D L (b^(p^n)) := by
    rw [← hab, map_mul, map_pow, map_pow]
    rw [← Nat.sub_add_cancel hq, pow_succ]
    field_simp
    simp only [Nat.sub_add_cancel hq]
  have ha : a*b^(p^n-1) ∈ order A D K L := by
    change IsSeparable K (algebraMap D L (a*b^(p^n-1)))
    rw [hid]
    exact Field.isSeparable_mul z.2 (hn b)
  refine ⟨⟨a*b^(p^n-1),ha⟩, ⟨b^(p^n),hn b⟩, ?_⟩
  apply Subtype.ext
  change (z : L) = algebraMap D L (a*b^(p^n-1)) / algebraMap D L (b^(p^n))
  rw [hid, mul_div_cancel_right₀]
  rw [map_pow]
  exact pow_ne_zero _ hb0

end Lech.SeparableOrder


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
-- module Solutions.OAIQ032_LECH.Multiplicity_RobertsSeparable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter
open scoped TensorProduct ENNReal Topology
namespace Lech.PerfectDomainStages
open Lech.RootTower Lech.Koszul
universe u
variable (h : ℕ) (k D : Type u) [Field k] [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D] [Algebra (MvPowerSeries (Fin h) k) D]
  [IsLocalHom (algebraMap (MvPowerSeries (Fin h) k) D)]
  [Module.Finite (MvPowerSeries (Fin h) k) D]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]
  (K L : Type u) [Field K] [Field L]
  [Algebra (MvPowerSeries (Fin h) k) K] [IsFractionRing (MvPowerSeries (Fin h) k) K]
  [Algebra (MvPowerSeries (Fin h) k) L] [Algebra D L] [IsScalarTower (MvPowerSeries (Fin h) k) D L]
  [Algebra K L] [IsScalarTower (MvPowerSeries (Fin h) k) K L] [IsFractionRing D L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [CharP K p] [CharP L p]

include K L in
 
theorem frobenius_shortComplex_homology_tendsto_zero
    (hdim : dimension D = h)
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField (MvPowerSeries (Fin h) k))
      (IsLocalRing.ResidueField D)))
    (F : CochainComplex (ModuleCat.{u} D) ℤ) (hF : IsFiniteHomologyComplex D F)
    (i : ℤ) (hi : i < 0) :
    Tendsto (fun n : ℕ => ((Module.length D ((frobeniusComplex D p n F).homology i)).toNat : ℝ) /
      ((p:ℝ)^n)^(dimension D)) atTop (𝓝 0) := by
  obtain ⟨a,ha,hbound⟩ := frobenius_homology_conductor_bound h k D p K L hdim hres F hF
  have hp0 : 0 < (p:ℝ) := by exact_mod_cast (Nat.Prime.pos (Fact.out : p.Prime))
  by_cases hu : IsUnit a
  · have hz (n : ℕ) : Module.length D ((frobeniusComplex D p n F).homology i) = 0 := by
      apply le_zero_iff.mp
      apply (hbound n i hi).trans
      let Q := (complexQuotient (Ideal.span {a}) (.up ℤ)).obj (frobeniusComplex D p n F)
      have he : a • 𝟙 Q = 0 := complexQuotient_annihilated (Ideal.span {a}) a
        (Ideal.subset_span (Set.mem_singleton a)) (frobeniusComplex D p n F)
      have hQ : IsZero Q := (IsZero.iff_id_eq_zero Q).mpr (hu.smul_eq_zero.mp he)
      have : Subsingleton (Q.homology i) := ModuleCat.isZero_iff_subsingleton.mp
        ((homologyFunctor (ModuleCat D) (.up ℤ) i).map_isZero hQ)
      exact le_of_eq (Module.length_eq_zero (R:=D) (M:=Q.homology i))
    simpa only [hz,ENat.toNat_zero,Nat.cast_zero,zero_div] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
  · obtain ⟨zs,hd,hzs,hprim⟩ := exists_small_quotient_parameters a
      (mem_nonZeroDivisors_of_ne_zero ha) hu
    apply squeeze_zero (g := fun n : ℕ =>
      ((Module.length D (((complexQuotient (Ideal.span {a}) (.up ℤ)).obj
        (frobeniusComplex D p n F)).homology i)).toNat : ℝ) / ((p:ℝ)^n)^(dimension D))
    · intro n; positivity
    · intro n
      apply (div_le_div_iff_of_pos_right (by positivity)).mpr
      exact_mod_cast ENat.toNat_le_toNat (hbound n i hi) (Module.length_ne_top_iff.mpr
        (frobenius_quotient_homology_finiteLength p F hF (Ideal.span {a}) n i))
    · exact frobenius_quotient_homology_tendsto_zero p F hF (Ideal.span {a}) zs hzs hprim hd i
end Lech.PerfectDomainStages

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RobertsNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace Lech.SeparableOrder
open Lech.RootTower Lech.PerfectDomainStages Filter
open scoped ENNReal Topology
universe u
variable (h : ℕ) (k D : Type u) [Field k] [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D]
  [Algebra (MvPowerSeries (Fin h) k) D]
  [IsLocalHom (algebraMap (MvPowerSeries (Fin h) k) D)]
  [Module.Finite (MvPowerSeries (Fin h) k) D]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]
  (K L : Type u) [Field K] [Field L]
  [Algebra (MvPowerSeries (Fin h) k) K] [IsFractionRing (MvPowerSeries (Fin h) k) K]
  [Algebra (MvPowerSeries (Fin h) k) L] [Algebra D L] [IsScalarTower (MvPowerSeries (Fin h) k) D L]
  [Algebra K L] [IsScalarTower (MvPowerSeries (Fin h) k) K L] [IsFractionRing D L]
  [FiniteDimensional K L] [CharP K p] [CharP L p]

include K L in
theorem frobenius_homology_tendsto_zero_oai
    (hf : Function.Injective (algebraMap (MvPowerSeries (Fin h) k) D))
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField (MvPowerSeries (Fin h) k))
      (IsLocalRing.ResidueField D)))
    (hdD : Lech.dimension D = h)
    (F : CochainComplex (ModuleCat.{u} D) ℤ) (hF : Lech.IsFiniteHomologyComplex D F)
    (i : ℤ) (hi : i < 0) :
    Tendsto (fun n : ℕ => ((Module.length D ((Lech.frobeniusComplex D p n F).homology i)).toNat : ℝ) /
      ((p:ℝ)^n)^(Lech.dimension D)) atTop (𝓝 0) := by
  let A := MvPowerSeries (Fin h) k
  let B := order A D K L
  let E := separableClosure K L
  let : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  let : IsNoetherianRing B.toSubring := inferInstanceAs (IsNoetherianRing B)
  let : IsLocalRing B.toSubring := inferInstanceAs (IsLocalRing B)
  let : IsLocalHom B.toSubring.subtype := inferInstanceAs (IsLocalHom (algebraMap B D))
  let : CharP B p := B.val.toRingHom.charP Subtype.val_injective p
  let : CharP E p := (algebraMap E L).charP (algebraMap E L).injective p
  let : IsLocalHom (algebraMap A B) := ⟨fun x hx =>
    isUnit_of_map_unit (algebraMap A D) x (by
      simpa only [← IsScalarTower.algebraMap_apply A B D] using hx.map (algebraMap B D))⟩
  let : Module.Finite B D := Module.Finite.of_restrictScalars_finite A B D
  have hfb : Function.Injective (algebraMap A B) := by
    intro x y hxy
    exact hf (by simpa only [← IsScalarTower.algebraMap_apply A B D] using
      (congrArg (algebraMap B D) hxy))
  have hresBD : Function.Surjective (algebraMap (IsLocalRing.ResidueField B)
      (IsLocalRing.ResidueField D)) := by
    intro x
    obtain ⟨a,ha⟩ := hres x
    exact ⟨algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) a,
      (IsScalarTower.algebraMap_apply _ _ _ a).symm.trans ha⟩
  have hresAB : Function.Surjective (algebraMap (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField B)) := by
    intro b
    obtain ⟨a,ha⟩ := hres (algebraMap (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField D) b)
    refine ⟨a,(algebraMap (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField D)).injective ?_⟩
    exact (IsScalarTower.algebraMap_apply _ _ _ a).symm.trans ha
  have hdim : Lech.dimension B = h := by
    have hd := Lech.ringKrullDim_eq_of_integral_injective (algebraMap A B)
      (Algebra.IsIntegral.isIntegral : (algebraMap A B).IsIntegral) hfb
    rw [Lech.PowerSeries.fin_dimension k h] at hd
    have hh := Lech.dimension_cast B
    rw [hd] at hh
    exact_mod_cast hh
  have hdimSub : Lech.dimension B.toSubring = h := hdim
  obtain ⟨e,he⟩ := uniform_power A D K L p
  let φ := Lech.FrobeniusIntermediate.powerMap p B.toSubring e he
  let G := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj F
  have hGB : Lech.IsFiniteHomologyComplex B G :=
    Lech.finiteHomology_extendScalars φ (hdim.trans hdD.symm)
      (Lech.FrobeniusIntermediate.map_radical_primary p B.toSubring e he
        (IsLocalRing.maximalIdeal D) (Ideal.IsPrime.radical inferInstance)) F hF
  have ht := Lech.PerfectDomainStages.frobenius_shortComplex_homology_tendsto_zero
    h k B p K E hdim hresAB G hGB i hi
  exact Lech.FrobeniusIntermediate.frobenius_homology_order_transfer p B.toSubring
    e he hresBD (hdim.trans hdD.symm) F hF i ht
end Lech.SeparableOrder

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.SeparableOrder.frobenius_homology_tendsto_zero_oai.{u} := @OAI.Lech.SeparableOrder.frobenius_homology_tendsto_zero_oai.{u}
