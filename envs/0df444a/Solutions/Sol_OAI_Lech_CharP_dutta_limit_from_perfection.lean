-- Prove2me | solution 1 for OAI.Lech.CharP.dutta_limit_from_perfection
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T20:58:04.652697+00:00
-- url     : https://prove2.me/submissions/9236c891-633c-4537-bdce-e739653edd13

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L006
import Definitions.Def_OAIQ032L017
import Definitions.Def_OAIQ032L018
import Theorems.Thm_OAI_Lech_CharP_real_frobeniusModule_limit
import Theorems.Thm_OAI_Lech_SeparableOrder_frobenius_homology_tendsto_zero

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechTorsionOf
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory

attribute [local instance] Classical.propDecidable


namespace Lech.AllModuleLength
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct DirectSum
universe u
variable {C : Type u} [CommRing C] (ell : AllModuleLength C)

lemma value_eq_of_linearEquiv {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module C M] [Module C N] (e : M ≃ₗ[C] N) :
    ell.value (ModuleCat.of C M) = ell.value (ModuleCat.of C N) := by
  apply le_antisymm
  · have : Mono (ModuleCat.ofHom e.toLinearMap) := (ModuleCat.mono_iff_injective _).mpr e.injective
    exact (ell.torsionLength ⊥).le_of_mono (ModuleCat.ofHom e.toLinearMap) ⟨1,by simp⟩
  · have : Mono (ModuleCat.ofHom e.symm.toLinearMap) := (ModuleCat.mono_iff_injective _).mpr e.symm.injective
    exact (ell.torsionLength ⊥).le_of_mono (ModuleCat.ofHom e.symm.toLinearMap) ⟨1,by simp⟩

end Lech.AllModuleLength


end

end OAI
end

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


namespace Lech.Normalization
variable {R S : Type*} [CommRing R] [CommRing S]

 
lemma dimension_le_of_integral (f : R →+* S) (hf : f.IsIntegral) :
    ringKrullDim S ≤ ringKrullDim R := by
  let : Algebra R S := f.toAlgebra
  let : Algebra.IsIntegral R S := ⟨hf⟩
  apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap f)
  intro p q hpq
  exact Ideal.IsIntegral.comap_lt_comap hpq

 
lemma injective_of_integral_dimension [IsDomain R] (f : R →+* S) (hf : f.IsIntegral)
    {h : ℕ} (hS : (h : WithBot ℕ∞) ≤ ringKrullDim S) (hR : ringKrullDim R ≤ h) :
    Function.Injective f := by
  apply (injective_iff_map_eq_zero f).mpr
  intro r hr
  by_contra hn
  have hd := dimension_le_of_integral f.kerLift hf.kerLift
  have hdrop := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk (RingHom.ker f))
    Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_iff_ne_zero.mpr hn)
    (Ideal.Quotient.eq_zero_iff_mem.mpr hr)
  have hh : (h : WithBot ℕ∞) + 1 ≤ h :=
    (add_le_add (hS.trans hd) le_rfl).trans (hdrop.trans hR)
  norm_cast at hh
  omega

end Lech.Normalization


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
variable {k D : Type*} [Field k] [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
  [Algebra k D]

lemma finite_primary_quotient (I : Ideal D) (hI : I.radical = maximalIdeal D)
    (hres : Function.Surjective (algebraMap k (ResidueField D))) : Module.Finite k (D ⧸ I) := by
  let : IsArtinianRing (D ⧸ I) := by
    apply IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing I
    rw [← Ideal.radical_minimalPrimes,hI,Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _
  let : IsArtinian D (D ⧸ I) := isArtinian_of_surjective_algebraMap (R := D ⧸ I) (M := D ⧸ I)
    (S := D) Ideal.Quotient.mk_surjective
  have hs : Function.Surjective (algebraMap (ResidueField k) (ResidueField D)) := by
    intro y
    obtain ⟨x,hx⟩ := hres y
    exact ⟨residue k x,hx⟩
  have hl : Module.length k (D ⧸ I) = Module.length D (D ⧸ I) := by
    rw [IsLocalRing.length_restrictScalars k D (D ⧸ I),Module.length_eq_of_surjective hs]
    simp
  have hfin : IsFiniteLength k (D ⧸ I) := Module.length_ne_top_iff.mp (by
    rw [hl]; exact Module.length_ne_top)
  let : IsNoetherian k (D ⧸ I) := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).1
  infer_instance

end Lech.Normalization


namespace Lech.Normalization
open IsLocalRing MvPowerSeries
variable {σ k D : Type*} [Fintype σ] [Field k] [CommRing D] [IsLocalRing D]
  [IsNoetherianRing D] [IsAdicComplete (maximalIdeal D) D]
  (φ : k →+* D) (hφ : Function.Surjective ((residue D).comp φ))
  (z : σ → D) (hz : ∀ i, z i ∈ maximalIdeal D)

include hφ in
 

theorem finite_parameter_algebra
    (hprim : (Ideal.span (Set.range z)).radical = maximalIdeal D) :
    let : Algebra (MvPowerSeries σ k) D :=
      (Lech.PowerSeries.eval φ (maximalIdeal D) z hz).toAlgebra
    Module.Finite (MvPowerSeries σ k) D := by
  let A := MvPowerSeries σ k
  let I := Lech.PowerSeries.variablesIdeal σ k
  let J : Ideal D := Ideal.span (Set.range z)
  let : IsDomain (MvPowerSeries σ k) := NoZeroDivisors.to_isDomain _
  let ψ := Lech.PowerSeries.eval φ (maximalIdeal D) z hz
  let : Algebra k D := φ.toAlgebra
  let : Algebra A D := ψ.toAlgebra
  let : IsScalarTower k A D := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro a
    exact (Lech.PowerSeries.eval_C φ (maximalIdeal D) z hz a).symm)
  have hmap : I.map (algebraMap A D) = J := by
    change (Ideal.span (Set.range (X : σ → A))).map (algebraMap A D) = J
    rw [Ideal.map_span,← Set.range_comp]
    apply congrArg Ideal.span
    exact congrArg Set.range (funext (fun i => Lech.PowerSeries.eval_X φ (maximalIdeal D) z hz i))
  have hJ : J ≤ maximalIdeal D := Ideal.span_le.mpr (Set.range_subset_iff.mpr hz)
  let : IsHausdorff I D := IsHausdorff.of_map (I := I) (J := maximalIdeal D) (by rw [hmap]; exact hJ)
  let : IsPrecomplete I A := (Lech.PowerSeries.complete_variables σ k).toIsPrecomplete
  let : Module.Finite k (D ⧸ J) := finite_primary_quotient J hprim hφ
  let : Module.Finite A (D ⧸ J) := Module.Finite.of_restrictScalars_finite k A (D ⧸ J)
  have hsub : I • (⊤ : Submodule A D) = J.restrictScalars A := by
    rw [← hmap]
    symm
    simpa only [smul_eq_mul,Ideal.mul_top,Submodule.restrictScalars_top] using
      Submodule.restrictScalars_map_smul_eq I (⊤ : Submodule D D)
  let e := (Submodule.quotEquivOfEq _ _ hsub).trans (Submodule.Quotient.restrictScalarsEquiv A J)
  let : Module.Finite A (D ⧸ (I • (⊤ : Submodule A D))) := Module.Finite.equiv e.symm
  exact Lech.AdicNakayama.finite_of_quotient I

end Lech.Normalization


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


namespace Lech.CoefficientField
variable (R : Type*) [CommRing R] (I : Ideal R) (p : ℕ) [Fact p.Prime] [CharP R p]
  [CharP (R ⧸ I) p] [PerfectRing (R ⧸ I) p]


variable [IsAdicComplete I R]



lemma sectionMap_mod (n : ℕ) (x : R ⧸ I) :
    Ideal.Quotient.mk (I^(p^n)) (sectionMap R I p x) = stage R I p n x :=
  IsAdicComplete.StrictMono.mk_liftRingHom _ _ _ _ x

 
theorem sectionMap_rightInverse : Function.RightInverse (sectionMap R I p) (Ideal.Quotient.mk I) := by
  intro x
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
  have h := sectionMap_mod R I p 0 (Ideal.Quotient.mk I a)
  have h0 := stage_pow_mk R I p 0 a
  apply Ideal.Quotient.eq.mpr
  have hh := Ideal.Quotient.eq.mp (h.trans (by simpa only [pow_zero,pow_one] using h0))
  simpa only [pow_zero,pow_one] using hh

end Lech.CoefficientField
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CoefficientFieldLocalSection
attribute [-instance] _root_.OAI.Lech.extendScalars_additive
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
open scoped Classical Pointwise
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
open scoped ENNReal ZeroObject
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open CategoryTheory
namespace Lech.CoefficientField
variable (R : Type*) [CommRing R] [IsDomain R] [IsLocalRing R]
  (p : ℕ) [Fact p.Prime] [CharP R p]
  [PerfectRing (IsLocalRing.ResidueField R) p]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]



lemma localSection_rightInverse :
    Function.RightInverse (localSection R p) (IsLocalRing.residue R) := by
  let : CharP (R ⧸ IsLocalRing.maximalIdeal R) p :=
    CharP.of_ringHom_of_ne_zero (Ideal.Quotient.mk _) p (Nat.Prime.ne_zero Fact.out)
  let : PerfectRing (R ⧸ IsLocalRing.maximalIdeal R) p :=
    inferInstanceAs (PerfectRing (IsLocalRing.ResidueField R) p)
  exact sectionMap_rightInverse R (IsLocalRing.maximalIdeal R) p

end Lech.CoefficientField


namespace Lech.Normalization
open IsLocalRing MvPowerSeries
variable {σ k D : Type*} [Fintype σ] [Field k] [CommRing D] [IsLocalRing D]
  [IsNoetherianRing D] [IsAdicComplete (maximalIdeal D) D]
  (φ : k →+* D) (hφ : Function.Surjective ((residue D).comp φ))
  (z : σ → D) (hz : ∀ i, z i ∈ maximalIdeal D)

include hφ in
lemma parameter_eval_finite (hprim : (Ideal.span (Set.range z)).radical = maximalIdeal D) :
    (Lech.PowerSeries.eval φ (maximalIdeal D) z hz).Finite :=
  finite_parameter_algebra φ hφ z hz hprim

include hφ in
lemma parameter_eval_injective (hprim : (Ideal.span (Set.range z)).radical = maximalIdeal D)
    (hdim : (Fintype.card σ : WithBot ℕ∞) ≤ ringKrullDim D) :
    Function.Injective (Lech.PowerSeries.eval φ (maximalIdeal D) z hz) := by
  let : IsDomain (MvPowerSeries σ k) := NoZeroDivisors.to_isDomain _
  let ψ := Lech.PowerSeries.eval φ (maximalIdeal D) z hz
  let : Algebra (MvPowerSeries σ k) D := ψ.toAlgebra
  let : Module.Finite (MvPowerSeries σ k) D := finite_parameter_algebra φ hφ z hz hprim
  exact injective_of_integral_dimension ψ (Algebra.IsIntegral.isIntegral)
    hdim (Lech.PowerSeries.dimension_le_variables σ k)

end Lech.Normalization


namespace Lech.Normalization
open IsLocalRing MvPowerSeries
variable (D : Type*) [CommRing D] [IsDomain D] [IsNoetherianRing D] [IsLocalRing D]
  [IsAdicComplete (maximalIdeal D) D]
  (p : ℕ) [Fact p.Prime] [CharP D p] [PerfectRing (ResidueField D) p]

include p in
 

theorem exists_finite_powerSeries_normalization :
    ∃ (n : ℕ) (ψ : MvPowerSeries (Fin n) (ResidueField D) →+* D),
      Function.Injective ψ ∧ ψ.Finite ∧ IsLocalHom ψ ∧
      Function.Surjective ((residue D).comp ψ) ∧ ringKrullDim D = n := by
  obtain ⟨n,z,hz,hprim,hdim⟩ := exists_parameters D
  let φ := Lech.CoefficientField.localSection D p
  have hφ : Function.Surjective ((residue D).comp φ) :=
    fun a => ⟨a,Lech.CoefficientField.localSection_rightInverse D p a⟩
  let ψ := Lech.PowerSeries.eval φ (maximalIdeal D) z hz
  have hfin : ψ.Finite := parameter_eval_finite φ hφ z hz hprim
  have hinj : Function.Injective ψ := parameter_eval_injective φ hφ z hz hprim (by
    simpa only [Fintype.card_fin,hdim] using (le_refl (n : WithBot ℕ∞)))
  have hint : ψ.IsIntegral := by
    let : Algebra (MvPowerSeries (Fin n) (ResidueField D)) D := ψ.toAlgebra
    let : Module.Finite (MvPowerSeries (Fin n) (ResidueField D)) D := hfin
    exact Algebra.IsIntegral.isIntegral
  refine ⟨n,ψ,hinj,hfin,hint.isLocalHom hinj,?_,hdim⟩
  intro a
  refine ⟨C a,?_⟩
  change residue D (Lech.PowerSeries.eval φ (maximalIdeal D) z hz (C a)) = a
  rw [Lech.PowerSeries.eval_C]
  exact Lech.CoefficientField.localSection_rightInverse D p a

end Lech.Normalization


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ZeroHomologyScalarExtension
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

variable [IsNoetherianRing R] [IsLocalRing R]
omit [IsNoetherianRing R] [IsLocalRing R] in
lemma IsFiniteHomologyComplex.d_zero_one_eq_zero
    {F : CochainComplex (ModuleCat.{u} R) ℤ} (hF : IsFiniteHomologyComplex R F) :
    F.d 0 1 = 0 :=
  (hF.bounded 1 (Or.inr (by omega))).eq_of_tgt _ _
end Lech

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

omit [IsLocalRing R] [IsNoetherianRing R] in
lemma duttaSequence_tendsto_of_homology_limits
    (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (L : ℝ)
    (hzero : Tendsto (fun n : ℕ => ((Module.length R ((frobeniusComplex R p n F).homology 0)).toNat : ℝ) /
      ((p:ℝ)^n)^(dimension R)) atTop (𝓝 L))
    (hneg : ∀ i : ℤ,i < 0 → Tendsto (fun n : ℕ =>
      ((Module.length R ((frobeniusComplex R p n F).homology i)).toNat : ℝ) /
        ((p:ℝ)^n)^(dimension R)) atTop (𝓝 0)) :
    Tendsto (duttaSequence R p F) atTop (𝓝 L) := by
  classical
  have hi (i : ℕ) : Tendsto (fun n : ℕ => (-1:ℝ)^i *
      (((Module.length R ((frobeniusComplex R p n F).homology (-(i:ℤ)))).toNat : ℝ) /
        ((p:ℝ)^n)^(dimension R))) atTop (𝓝 (if i=0 then L else 0)) := by
    by_cases h : i=0
    · subst i
      simpa using hzero
    · have hlt : -(i:ℤ) < 0 := by omega
      simpa only [h,ite_false,mul_zero] using (hneg (-(i:ℤ)) hlt).const_mul ((-1:ℝ)^i)
  have hsum := tendsto_finsetSum (Finset.range (dimension R+1)) (fun i _ => hi i)
  simp only [Finset.sum_ite_eq',Finset.mem_range,Nat.succ_pos,ite_true] at hsum
  apply hsum.congr
  intro n
  unfold duttaSequence shortEuler
  rw [frobenius_weight_eq,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [div_eq_mul_inv]
  ring

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RobertsPerfectResidue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace Lech.CharP
open Lech.RootTower Lech.PerfectDomainStages Lech.Koszul IsLocalRing Filter
open scoped ENNReal Topology nonZeroDivisors
universe u
variable (D : Type u) [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D] [IsAdicComplete (maximalIdeal D) D]
  (p : ℕ) [Fact p.Prime] [CharP D p] [PerfectRing (ResidueField D) p]

theorem frobenius_homology_tendsto_zero
    (F : CochainComplex (ModuleCat.{u} D) ℤ) (hF : Lech.IsFiniteHomologyComplex D F)
    (i : ℤ) (hi : i < 0) :
    Tendsto (fun n : ℕ => ((Module.length D ((Lech.frobeniusComplex D p n F).homology i)).toNat : ℝ) /
      ((p:ℝ)^n)^(Lech.dimension D)) atTop (𝓝 0) := by
  obtain ⟨h,ψ,hψ,hfin,hloc,hres,hd⟩ :=
    Lech.Normalization.exists_finite_powerSeries_normalization D p
  have hdim : Lech.dimension D = h := by
    have hd' := Lech.dimension_cast D
    rw [hd] at hd'
    exact_mod_cast hd'
  let k := ResidueField D
  let : CharP k p := CharP.of_ringHom_of_ne_zero (residue D) p
    (Nat.Prime.ne_zero Fact.out)
  let A := MvPowerSeries (Fin h) k
  let C := PerfectClosure D p
  let P := PerfectClosure A p
  let : IsDomain A := NoZeroDivisors.to_isDomain _
  let : Algebra A D := ψ.toAlgebra
  let : Module.Finite A D := hfin
  let : IsLocalHom (algebraMap A D) := hloc
  have hf : Function.Injective (algebraMap A D) := hψ
  have hres' : Function.Surjective (algebraMap (ResidueField A) (ResidueField D)) := by
    intro b
    obtain ⟨a,ha⟩ := hres b
    refine ⟨residue A a,?_⟩
    rw [ResidueField.algebraMap_residue]
    exact ha
  let : FaithfulSMul A D := (faithfulSMul_iff_algebraMap_injective A D).mpr hf
  let K := FractionRing A
  let L := FractionRing D
  let : Algebra K L := FractionRing.liftAlgebra A L
  let : IsScalarTower A K L := FractionRing.isScalarTower_liftAlgebra A L
  let : FiniteDimensional K L := Module.Finite.of_isLocalization A D A⁰
  exact Lech.SeparableOrder.frobenius_homology_tendsto_zero h k D p K L hf hres' hdim F hF i hi
end Lech.CharP

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_DuttaPerfectResidue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter
open scoped Topology ENNReal
namespace Lech.CharP
universe u
variable (D : Type u) [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D] [IsAdicComplete (IsLocalRing.maximalIdeal D) D]
  (p : ℕ) [Fact p.Prime] [CharP D p] [PerfectRing (IsLocalRing.ResidueField D) p]

lemma dutta_limit_from_perfection_oai (F : CochainComplex (ModuleCat.{u} D) ℤ)
    (hF : IsFiniteHomologyComplex D F) (ell : AllModuleLength (PerfectClosure D p))
    (hfinite : ell.value ((ModuleCat.extendScalars (PerfectClosure.of D p)).obj
      (F.homology 0)) ≠ ⊤)
    (hlim : Tendsto (fun n : ℕ => ((p : ℝ≥0∞)^(n*dimension D))⁻¹ *
      (Module.length D (FrobeniusModule D p n (F.homology 0))).toENNReal) atTop
      (𝓝 (ell.value ((ModuleCat.extendScalars (PerfectClosure.of D p)).obj (F.homology 0))))) :
    Tendsto (duttaSequence D p F) atTop
      (𝓝 ((ell.value ((((ModuleCat.extendScalars (PerfectClosure.of D p)).mapHomologicalComplex
        (.up ℤ)).obj F).homology 0)).toReal)) := by
  have hz := hF.d_zero_one_eq_zero
  rw [ell.value_eq_of_linearEquiv (scalarExtensionZeroHomologyIso (PerfectClosure.of D p) F hz).toLinearEquiv]
  apply duttaSequence_tendsto_of_homology_limits p F
  · apply (real_frobeniusModule_limit D p (F.homology 0) (hF.homology_finite_length 0)
      _ hfinite hlim).congr
    intro n
    have he := (scalarExtensionZeroHomologyIso (iterateFrobenius D p n) F hz).toLinearEquiv.length_eq
    change ((Module.length D (FrobeniusModule D p n (F.homology 0))).toNat : ℝ) / _ = _
    change Module.length D ((frobeniusComplex D p n F).homology 0) =
      Module.length D (FrobeniusModule D p n (F.homology 0)) at he
    rw [he]
  · exact frobenius_homology_tendsto_zero D p F hF

end Lech.CharP

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.CharP.dutta_limit_from_perfection_oai.{u} := @OAI.Lech.CharP.dutta_limit_from_perfection_oai.{u}
