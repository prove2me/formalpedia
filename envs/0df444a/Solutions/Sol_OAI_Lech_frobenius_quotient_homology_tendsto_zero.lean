-- Prove2me | solution 1 for OAI.Lech.frobenius_quotient_homology_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:08:26.87143+00:00
-- url     : https://prove2.me/submissions/6e126638-7928-4c8e-98ea-81a0c7ebe478

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L014
import Theorems.Thm_OAI_Lech_frobenius_quotient_homology_bound

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FiniteModuleTensor
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal
namespace Lech
variable {A : Type*} [CommRing A]

lemma length_le_quotient_generators {N : Type*} [AddCommGroup N] [Module A N]
    (I : Ideal A) (hI : I ≤ Module.annihilator A N)
    {b : ℕ} (f : (Fin b → A) →ₗ[A] N) (hf : Function.Surjective f) :
    Module.length A N ≤ b * Module.length A (A ⧸ I) := by
  classical
  let P := Submodule.pi Set.univ (fun _ : Fin b => I)
  have hP : P ≤ f.ker := by
    intro x hx
    change f x = 0
    rw [pi_eq_sum_univ x, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [map_smul]
    exact Module.mem_annihilator.mp (hI (hx i (Set.mem_univ i))) _
  let q := P.liftQ f hP
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨y,rfl⟩ := hf x
    exact ⟨P.mkQ y,rfl⟩
  calc
    Module.length A N ≤ Module.length A ((Fin b → A) ⧸ P) :=
      Module.length_le_of_surjective q hq
    _ = Module.length A (Fin b → A ⧸ I) :=
      (Submodule.quotientPi (fun _ : Fin b => I)).length_eq
    _ = _ := by simp

open Filter
open scoped Topology


end Lech

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


namespace Lech



theorem quotient_length_ne_top (A : Type*) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (N : ℕ) :
    Module.length A (A ⧸ (IsLocalRing.maximalIdeal A) ^ N) ≠ ⊤ := by
  by_cases hN : N = 0
  · subst N
    simp
  · let I := (IsLocalRing.maximalIdeal A) ^ N
    have hp : IsLocalRing.maximalIdeal A ∈ I.minimalPrimes := by
      rw [← Ideal.radical_minimalPrimes, Ideal.radical_pow _ hN,
        Ideal.IsPrime.radical inferInstance, Ideal.minimalPrimes_eq_subsingleton_self]
      exact Set.mem_singleton _
    let : IsArtinianRing (A ⧸ I) :=
      IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing I hp
    rw [Module.length_eq_of_surjective (R := A ⧸ I)
      (by simpa only [Ideal.Quotient.algebraMap_eq] using
        (Ideal.Quotient.mk_surjective (I := I)))]
    exact Module.length_ne_top


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


namespace Lech
variable (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

omit [IsNoetherianRing R] [IsLocalRing R] in
lemma length_quotient_le {I J : Ideal R} (h : I ≤ J) :
    Module.length R (R ⧸ J) ≤ Module.length R (R ⧸ I) := by
  let f := I.mapQ J LinearMap.id h
  apply Module.length_le_of_surjective f
  intro q
  obtain ⟨r, rfl⟩ := J.mkQ_surjective q
  exact ⟨I.mkQ r, rfl⟩

end Lech

open scoped BigOperators
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_KoszulConeFunctor
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


namespace Lech.Koszul
open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
universe u
variable {R : Type u} [CommRing R]

lemma tensor_terms_finite (zs : List R) (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hF : ∀ i, Module.Finite R (F.X i)) : ∀ i, Module.Finite R ((tensor zs F).X i) := by
  induction zs with
  | nil => exact hF
  | cons a zs ih =>
    intro i
    let := ih (i+1)
    let := ih i
    exact Module.Finite.equiv (coneTermEquiv (tensor zs F) a i).symm

end Lech.Koszul


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealGradedLengthPiece
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


namespace Lech.Primary
open Filter
open scoped Topology
variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

lemma exists_maximal_pow_le (I : Ideal R) (hI : I.radical = IsLocalRing.maximalIdeal R) :
    ∃ a : ℕ, (IsLocalRing.maximalIdeal R) ^ a ≤ I := by
  simpa only [hI] using I.exists_radical_pow_le_of_fg I.radical.fg_of_isNoetherianRing

lemma length_ne_top (I : Ideal R) (hI : I.radical = IsLocalRing.maximalIdeal R) (N : ℕ) :
    Module.length R (R ⧸ I ^ N) ≠ ⊤ := by
  obtain ⟨a, ha⟩ := exists_maximal_pow_le I hI
  have hle := Lech.length_quotient_le R (show
    (IsLocalRing.maximalIdeal R) ^ (a * N) ≤ I ^ N by
      rw [pow_mul]
      exact pow_le_pow_left' ha N)
  exact ne_top_of_le_ne_top (Lech.quotient_length_ne_top R (a * N)) hle

end Lech.Primary


open CategoryTheory
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusFiniteLength
attribute [-instance] _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech
open scoped TensorProduct
universe u

lemma finiteLength_of_primary_annihilator {S N : Type*} [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] [AddCommGroup N] [Module S N] [Module.Finite S N]
    (I : Ideal S) (hI : I.radical = IsLocalRing.maximalIdeal S)
    (hIN : I ≤ Module.annihilator S N) : IsFiniteLength S N := by
  obtain ⟨b,f,hf⟩ := Module.Finite.exists_fin' S N
  apply Module.length_ne_top_iff.mp
  have hIfin := Lech.Primary.length_ne_top I hI 1
  rw [pow_one] at hIfin
  exact ne_top_of_le_ne_top (WithTop.mul_ne_top (ENat.natCast_ne_top b) hIfin)
    (length_le_quotient_generators I hIN f hf)

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusHomologyFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
namespace Lech
universe u
variable {R : Type u} [CommRing R]

lemma finite_shortComplex_homology [IsNoetherianRing R]
    (S : ShortComplex (ModuleCat.{u} R)) [Module.Finite R S.X₂] :
    Module.Finite R S.homology := by
  let : Module.Finite R S.moduleCatLeftHomologyData.H := by
    change Module.Finite R ((LinearMap.ker S.g.hom) ⧸ LinearMap.range S.moduleCatToCycles)
    infer_instance
  exact Module.Finite.equiv S.moduleCatHomologyIso.toLinearEquiv.symm

lemma finite_cochain_homology [IsNoetherianRing R]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) [Module.Finite R (F.X i)] :
    Module.Finite R (F.homology i) := by
  let : Module.Finite R (F.sc i).X₂ := by
    change Module.Finite R (F.X i)
    infer_instance
  exact finite_shortComplex_homology (F.sc i)

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_KoszulQuotientFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
namespace Lech.Koszul
universe u
variable {R : Type u} [CommRing R]

lemma entryIdeal_powers_radical (zs : List R) (a : ℕ) (ha : 0 < a) :
    (entryIdeal (zs.map (fun z => z^a))).radical = (entryIdeal zs).radical := by
  apply le_antisymm
  · apply Ideal.radical_mono
    apply Ideal.span_le.mpr
    intro r hr
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hr
    have hm : z∈entryIdeal zs := Ideal.subset_span hz
    exact (entryIdeal zs).pow_mem_of_pow_mem
      (show z^1 ∈ entryIdeal zs by simpa only [pow_one] using hm) ha
  · apply Ideal.radical_le_radical_iff.mpr
    apply Ideal.span_le.mpr
    intro z hz
    exact ⟨a,Ideal.subset_span (List.mem_map.mpr ⟨z,hz,rfl⟩)⟩

lemma sup_entryIdeal_powers_radical (I : Ideal R) (zs : List R) (a : ℕ) (ha : 0<a) :
    (I ⊔ entryIdeal (zs.map (fun z => z^a))).radical = (I ⊔ entryIdeal zs).radical := by
  rw [Ideal.radical_sup I,entryIdeal_powers_radical zs a ha,← Ideal.radical_sup]

lemma quotient_tensor_annihilator (I : Ideal R) (zs : List R)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    I ⊔ entryIdeal zs ≤ Module.annihilator R
      ((tensor zs ((complexQuotient I (.up ℤ)).obj F)).homology i) := by
  apply sup_le
  · intro x hx
    exact scalar_annihilates_homology _ x
      (tensorScalarHomotopy x zs (quotient_scalar_zero I F x hx)) i
  · exact tensor_homology_annihilator zs _ i

lemma finite_moduleQuotient (I : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M] :
    Module.Finite R ((moduleQuotient I).obj M) := by
  change Module.Finite R (M ⧸ I • (⊤ : Submodule R M))
  infer_instance

lemma single_terms_finite (M : ModuleCat.{u} R) [Module.Finite R M] (j k : ℤ) :
    Module.Finite R (((single (ModuleCat R) (.up ℤ) j).obj M).X k) := by
  by_cases hk : k=j
  · subst k
    exact Module.Finite.equiv (singleObjXSelf (.up ℤ) j M).toLinearEquiv.symm
  · have := ModuleCat.isZero_iff_subsingleton.mp (isZero_single_obj_X (.up ℤ) j M k hk)
    infer_instance

lemma quotient_tensor_single_finiteLength [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (zs : List R)
    (hI : (I ⊔ entryIdeal zs).radical = IsLocalRing.maximalIdeal R) (j i : ℤ) :
    IsFiniteLength R ((tensor zs ((complexQuotient I (.up ℤ)).obj
      ((single (ModuleCat R) (.up ℤ) j).obj (ModuleCat.of R R)))).homology i) := by
  let F := (single (ModuleCat.{u} R) (.up ℤ) j).obj (ModuleCat.of R R)
  have hfin (k : ℤ) : Module.Finite R (((complexQuotient I (.up ℤ)).obj F).X k) := by
    have : Module.Finite R (F.X k) := single_terms_finite _ j k
    exact finite_moduleQuotient I (F.X k)
  have := tensor_terms_finite zs _ hfin i
  have := finite_cochain_homology (tensor zs ((complexQuotient I (.up ℤ)).obj F)) i
  exact finiteLength_of_primary_annihilator _ hI (quotient_tensor_annihilator I zs F i)
end Lech.Koszul

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusHomologySmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex Filter
open scoped Topology
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

lemma frobenius_quotient_homology_nat_bound
    (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsFiniteHomologyComplex R F)
    (I : Ideal R) (zs : List R) (hzs : ∀ z∈zs,z∈IsLocalRing.maximalIdeal R)
    (hI : (I ⊔ Koszul.entryIdeal zs).radical = IsLocalRing.maximalIdeal R) (i : ℤ) :
    ∃ C : ℕ, ∀ n,
      (Module.length R (((complexQuotient I (.up ℤ)).obj
        (frobeniusComplex R p n F)).homology i)).toNat ≤ (p^n)^zs.length * C := by
  obtain ⟨a,ha,hbound⟩ := frobenius_quotient_homology_bound p F hF I zs hzs
  let L : ℕ∞ := ∑ k∈Finset.range (dimension R+1),
    Module.finrank R (F.X (-(dimension R : ℤ)+k)) • Module.length R
      ((Koszul.tensor (zs.map (fun z => z^a)) ((complexQuotient I (.up ℤ)).obj
        ((single (ModuleCat R) (.up ℤ) (-(dimension R : ℤ)+k)).obj
          (ModuleCat.of R R)))).homology i)
  have hL : L ≠ ⊤ := by
    apply ENat.sum_ne_top.mpr
    intro k hk
    have hf := Koszul.quotient_tensor_single_finiteLength I (zs.map (fun z => z^a))
      (by rw [Koszul.sup_entryIdeal_powers_radical I zs a ha]; exact hI)
      (-(dimension R:ℤ)+k) i
    have hl := Module.length_ne_top_iff.mpr hf
    rw [nsmul_eq_mul]
    exact WithTop.mul_ne_top (ENat.natCast_ne_top _) hl
  refine ⟨L.toNat,fun n => ?_⟩
  have h := ENat.toNat_le_toNat (hbound n i)
    (show ((p^n)^zs.length) • L ≠ ⊤ by
      rw [nsmul_eq_mul]
      exact WithTop.mul_ne_top (ENat.natCast_ne_top _) hL)
  simpa only [nsmul_eq_mul,ENat.toNat_mul,ENat.toNat_natCast,L] using h

lemma tendsto_normalized_polynomial (p r d : ℕ) (hp : 1 < p) (hr : r < d) (C : ℝ) :
    Tendsto (fun n : ℕ => C * ((p:ℝ)^n)^r / ((p:ℝ)^n)^d) atTop (𝓝 0) := by
  have hp1 : 1 < (p:ℝ) := by exact_mod_cast hp
  have hp0 : 0 < (p:ℝ) := by positivity
  have hratio : 0 ≤ ((p:ℝ)^r / (p:ℝ)^d) := by positivity
  have hlt : (p:ℝ)^r / (p:ℝ)^d < 1 := by
    apply (div_lt_one (by positivity)).mpr
    exact pow_lt_pow_right₀ hp1 hr
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hratio hlt).const_mul C
  convert ht using 1
  · ext n
    rw [div_pow,← pow_mul,← pow_mul]
    simp only [Nat.mul_comm n, pow_mul]
    ring
  · simp

 

theorem frobenius_quotient_homology_tendsto_zero_oai
    (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsFiniteHomologyComplex R F)
    (I : Ideal R) (zs : List R) (hzs : ∀ z∈zs,z∈IsLocalRing.maximalIdeal R)
    (hI : (I ⊔ Koszul.entryIdeal zs).radical = IsLocalRing.maximalIdeal R)
    (hd : zs.length < dimension R) (i : ℤ) :
    Tendsto (fun n : ℕ =>
      ((Module.length R (((complexQuotient I (.up ℤ)).obj
        (frobeniusComplex R p n F)).homology i)).toNat : ℝ) /
          ((p:ℝ)^n)^(dimension R)) atTop (𝓝 0) := by
  have hp0 : 0 < (p:ℝ) := by exact_mod_cast (Nat.Prime.pos (Fact.out : p.Prime))
  obtain ⟨C,hC⟩ := frobenius_quotient_homology_nat_bound p F hF I zs hzs hI i
  apply squeeze_zero
  · intro n; positivity
  · intro n
    apply (div_le_div_iff_of_pos_right (by positivity)).mpr
    have hc : ((Module.length R (((complexQuotient I (.up ℤ)).obj
        (frobeniusComplex R p n F)).homology i)).toNat : ℝ) ≤
        (((p^n)^zs.length * C : ℕ):ℝ) := by exact_mod_cast hC n
    simpa only [Nat.cast_mul,Nat.cast_pow,mul_comm] using hc
  · simpa only [mul_comm (C:ℝ)] using tendsto_normalized_polynomial p zs.length (dimension R)
      (Nat.Prime.one_lt Fact.out) hd C
end Lech

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.frobenius_quotient_homology_tendsto_zero_oai.{u} := @OAI.Lech.frobenius_quotient_homology_tendsto_zero_oai.{u}
