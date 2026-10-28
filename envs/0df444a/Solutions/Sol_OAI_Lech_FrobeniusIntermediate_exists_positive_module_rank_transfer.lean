-- Prove2me | solution 1 for OAI.Lech.FrobeniusIntermediate.exists_positive_module_rank_transfer
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:01:10.267994+00:00
-- url     : https://prove2.me/submissions/3c6af3e1-05ac-4aab-9810-e25bc3d9a7af

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L000
import Definitions.Def_OAIQ032L004
import Theorems.Thm_OAI_Lech_exists_frobenius_tensor_transfer
import Theorems.Thm_OAI_Lech_finiteLength_primary_annihilator

section
-- module Solutions.OAIQ032_LECH.Multiplicity_NormalizedLengthTrivialRelation
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.extendScalars_additive
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


namespace Lech.NormalizedLength
variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]

lemma map_le_annihilator_baseChange (I : Ideal R)
    (hI : I ≤ Module.annihilator R M) :
    I.map (algebraMap R S) ≤ Module.annihilator S (S ⊗[R] M) := by
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  apply Module.mem_annihilator.mpr
  intro x
  induction x using OAI.tensorInductionOn with
  | tmul s m =>
    rw [IsScalarTower.algebraMap_smul S r, TensorProduct.smul_tmul',
      TensorProduct.smul_tmul, Module.mem_annihilator.mp (hI hr) m,
      TensorProduct.tmul_zero]
  | add x y hx hy => simp only [smul_add, hx, hy, add_zero]

end Lech.NormalizedLength


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootTowerLengthEq
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.extendScalars_additive
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
namespace Lech.RootTower
open scoped ENNReal TensorProduct
variable {A D : Type*} [CommRing A] [CommRing D] [IsLocalRing A] [IsLocalRing D]
  [Algebra A D] [IsLocalHom (algebraMap A D)]

lemma length_eq_of_residue_surjective
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField D)))
    (M : Type*) [AddCommGroup M] [Module A M] [Module D M] [IsScalarTower A D M] :
    Module.length A M = Module.length D M := by
  rw [IsLocalRing.length_restrictScalars A D M,
    Module.length_eq_of_surjective (R := IsLocalRing.ResidueField D) hres]
  simp

end Lech.RootTower


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusModule
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech
open scoped TensorProduct

lemma finite_extendScalars {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (M : ModuleCat R) [Module.Finite R M] :
    Module.Finite S ((ModuleCat.extendScalars f).obj M) := by
  let := f.toAlgebra
  change Module.Finite S (S ⊗[R] M)
  infer_instance


instance finite_frobeniusModule (D : Type*) [CommRing D] (p : ℕ) [Fact p.Prime] [CharP D p]
    (n : ℕ) (M : ModuleCat D) [Module.Finite D M] :
    Module.Finite D (FrobeniusModule D p n M) :=
  finite_extendScalars (iterateFrobenius D p n) M
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FiniteModuleTensor
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.extendScalars_additive
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
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.extendScalars_additive
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
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.extendScalars_additive
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
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusIntermediatePowerMap
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
lemma extendScalars_annihilator {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (M : ModuleCat.{u} R) (I : Ideal R)
    (hI : I ≤ Module.annihilator R M) :
    I.map φ ≤ Module.annihilator S ((ModuleCat.extendScalars φ).obj M) := by
  let := φ.toAlgebra
  change I.map φ ≤ Module.annihilator S (S ⊗[R] M)
  exact Lech.NormalizedLength.map_le_annihilator_baseChange I hI

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

lemma finiteLength_extendScalars_of_primary {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S]
    (φ : R →+* S) (M : ModuleCat.{u} R) [Module.Finite R M] (I : Ideal R)
    (hI : I ≤ Module.annihilator R M) (hφ : (I.map φ).radical = IsLocalRing.maximalIdeal S) :
    IsFiniteLength S ((ModuleCat.extendScalars φ).obj M) := by
  have := finite_extendScalars φ M
  exact finiteLength_of_primary_annihilator _ hφ (extendScalars_annihilator φ M I hI)

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusOrderTransfer
attribute [-instance] _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal Topology
open Filter CategoryTheory
namespace Lech.FrobeniusIntermediate
universe u
variable {D : Type u} [CommRing D] [IsDomain D] [IsNoetherianRing D] [IsLocalRing D]
  (p : ℕ) [Fact p.Prime] [CharP D p]
  (B : Subring D) [IsLocalRing B] [IsNoetherianRing B] [IsLocalHom B.subtype]
  [Module.Finite B D]



omit [IsNoetherianRing D] in
theorem exists_positive_module_rank_transfer_oai [IsNoetherianRing D] :
    ∃ r : ℕ, 0 < r ∧ ∀ (e : ℕ) (he : ∀ x : D, x^(p^e) ∈ B)
      (_hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField D)))
      (M : ModuleCat.{u} D), IsFiniteLength D M → ∀ a : ℝ≥0∞,
      Tendsto (fun n => ((p : ℝ≥0∞)^(n*Lech.dimension B))⁻¹ *
        (Module.length B (Lech.FrobeniusModule B p n
          ((ModuleCat.extendScalars (powerMap p B e he)).obj M))).toENNReal)
        atTop (𝓝 a) →
      Tendsto (fun n => ((p : ℝ≥0∞)^(n*Lech.dimension B))⁻¹ *
        (Module.length D (Lech.FrobeniusModule D p n M)).toENNReal)
        atTop (𝓝 (((p : ℝ≥0∞)^(e*Lech.dimension B))⁻¹ * ((r : ℝ≥0∞)*a))) := by
  obtain ⟨r,hr,h⟩ := Lech.exists_frobenius_tensor_transfer B D p (by
    intro g hg hz
    have hc := LinearMap.congr_fun hz (1 : D)
    change (g : D) * 1 = 0 at hc
    simp only [mul_one] at hc
    exact hg (Subtype.val_injective hc))
  refine ⟨r,hr,?_⟩
  intro e he hres M hM a ha
  let N := (ModuleCat.extendScalars (powerMap p B e he)).obj M
  have := (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).1
  obtain ⟨I,hI,hIM⟩ := Lech.finiteLength_primary_annihilator hM
  have hN : IsFiniteLength B N :=
    Lech.finiteLength_extendScalars_of_primary (powerMap p B e he) M I hIM
      (map_radical_primary p B e he I hI)
  have ht := h N hN a ha
  have ht' : Tendsto (fun n => ((p : ℝ≥0∞)^(n*Lech.dimension B))⁻¹ *
      (Module.length D (Lech.FrobeniusModule D p (e+n) M)).toENNReal)
      atTop (𝓝 ((r : ℝ≥0∞)*a)) := by
    apply ht.congr
    intro n
    congr 1
    rw [Lech.RootTower.length_eq_of_residue_surjective hres]
    exact congrArg ENat.toENNReal
      (frobeniusModule_order_iso p B e he M n).toLinearEquiv.length_eq
  have hp0 : (p : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hwfin : ((p : ℝ≥0∞)^(e*Lech.dimension B))⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (pow_ne_zero _ hp0)
  have ht'' := ENNReal.Tendsto.const_mul (a := ((p : ℝ≥0∞)^(e*Lech.dimension B))⁻¹)
    ht' (Or.inr hwfin)
  apply (tendsto_add_atTop_iff_nat e).mp
  apply ht''.congr
  intro n
  rw [Nat.add_comm n e,Nat.add_mul,pow_add,
    ENNReal.mul_inv (Or.inl (pow_ne_zero _ hp0)) (Or.inl (by simp)),mul_assoc]
end Lech.FrobeniusIntermediate

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.FrobeniusIntermediate.exists_positive_module_rank_transfer_oai.{u} := @OAI.Lech.FrobeniusIntermediate.exists_positive_module_rank_transfer_oai.{u}
