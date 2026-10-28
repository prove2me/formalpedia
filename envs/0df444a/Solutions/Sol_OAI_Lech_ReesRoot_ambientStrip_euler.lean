-- Prove2me | solution 1 for OAI.Lech.ReesRoot.ambientStrip_euler
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T23:20:20.297829+00:00
-- url     : https://prove2.me/submissions/c30ca46b-1e91-4803-8021-a33147660aa1

import Mathlib
import Definitions.Def_OAIQ032L037
import Theorems.Thm_OAI_Lech_ReesRoot_fibreCech_homology

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FiniteComplexTopInclusion
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.module _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
namespace Lech

section


universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]


variable {R : Type u} [CommRing R] {I : Ideal R}
namespace TorsionLength
variable (ℓ : TorsionLength I)

lemma eq_of_iso {M N : ModuleCat.{u} R} (e : M ≅ N)
    (hM : powerTorsion I M) (hN : powerTorsion I N) : ℓ.value M = ℓ.value N :=
  le_antisymm (ℓ.le_of_mono e.hom hN) (ℓ.le_of_mono e.inv hM)

lemma eq_of_isoModSerre {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (hM : powerTorsion I M) (hN : powerTorsion I N)
    (hf : ℓ.zeroClass.isoModSerre f) : ℓ.value M = ℓ.value N := by
  have h₁ : (ShortComplex.kernelSequence (Abelian.factorThruImage f)).ShortExact :=
    { exact := ShortComplex.kernelSequence_exact _
      epi_g := (inferInstance : Epi (Abelian.factorThruImage f)) }
  have h₂ : (ShortComplex.cokernelSequence (Abelian.image.ι f)).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact _
      mono_f := (inferInstance : Mono (Abelian.image.ι f)) }
  have e₁ := ℓ.additive h₁ hM
  have e₂ := ℓ.additive h₂ hN
  have hker := hf.1.isoModSerre_factorThruImage.1.2
  have hcoker := hf.2.isoModSerre_image_ι.2.2
  dsimp only [ShortComplex.kernelSequence, ShortComplex.cokernelSequence] at e₁ e₂
  rw [hker, zero_add] at e₁
  rw [hcoker, add_zero] at e₂
  exact e₁.trans e₂.symm

end TorsionLength
end


universe u
variable {R : Type u} [CommRing R] {I : Ideal R}

lemma powerTorsion_prod {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N]
    (hM : powerTorsion I (ModuleCat.of R M)) (hN : powerTorsion I (ModuleCat.of R N)) :
    powerTorsion I (ModuleCat.of R (M × N)) := by
  obtain ⟨a, ha⟩ := hM
  obtain ⟨b, hb⟩ := hN
  refine ⟨max a b, ?_⟩
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  ext
  · exact Module.mem_annihilator.mp (ha (Ideal.pow_le_pow_right (le_max_left a b) hr)) x.1
  · exact Module.mem_annihilator.mp (hb (Ideal.pow_le_pow_right (le_max_right a b) hr)) x.2

lemma powerTorsion_fin {M : Type u} [AddCommGroup M] [Module R M] (n : ℕ)
    (hM : powerTorsion I (ModuleCat.of R M)) :
    powerTorsion I (ModuleCat.of R (Fin n → M)) := by
  obtain ⟨a, ha⟩ := hM
  refine ⟨a, ?_⟩
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  ext i
  exact Module.mem_annihilator.mp (ha hr) (x i)

namespace TorsionLength
variable (ℓ : TorsionLength I)

lemma additive_linear {M N P : Type u} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [Module R M] [Module R N] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hf : Function.Injective f)
    (hg : Function.Surjective g) (he : Function.Exact f g)
    (ht : powerTorsion I (ModuleCat.of R N)) :
    ℓ.value (ModuleCat.of R N) =
      ℓ.value (ModuleCat.of R M) + ℓ.value (ModuleCat.of R P) := by
  let S := ShortComplex.moduleCatMk f g (LinearMap.range_le_ker_iff.mp
    ((LinearMap.exact_iff.mp he).symm.le))
  have hS : S.ShortExact :=
    { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr he
      mono_f := (ModuleCat.mono_iff_injective _).mpr hf
      epi_g := (ModuleCat.epi_iff_surjective _).mpr hg }
  exact ℓ.additive hS ht

lemma value_prod {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N]
    (hM : powerTorsion I (ModuleCat.of R M)) (hN : powerTorsion I (ModuleCat.of R N)) :
    ℓ.value (ModuleCat.of R (M × N)) =
      ℓ.value (ModuleCat.of R M) + ℓ.value (ModuleCat.of R N) := by
  apply ℓ.additive_linear (LinearMap.inl R M N) (LinearMap.snd R M N)
  · intro x y h
    exact congrArg Prod.fst h
  · intro n
    exact ⟨(0, n), rfl⟩
  · intro ⟨m, n⟩
    simp only [LinearMap.snd_apply]
    constructor
    · intro hn
      exact ⟨m, by simp [hn]⟩
    · rintro ⟨x, hx⟩
      exact (congrArg Prod.snd hx).symm
  · exact powerTorsion_prod hM hN

lemma value_linearEquiv {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (e : M ≃ₗ[R] N)
    (hN : powerTorsion I (ModuleCat.of R N)) :
    ℓ.value (ModuleCat.of R M) = ℓ.value (ModuleCat.of R N) := by
  let e' := e.toModuleIso
  exact ℓ.eq_of_iso e' ((powerTorsion I).prop_of_iso e'.symm hN) hN

lemma value_fin {M : Type u} [AddCommGroup M] [Module R M]
    (hM : powerTorsion I (ModuleCat.of R M)) (n : ℕ) :
    ℓ.value (ModuleCat.of R (Fin n → M)) = n • ℓ.value (ModuleCat.of R M) := by
  induction n with
  | zero =>
    rw [ℓ.zero (ModuleCat.isZero_iff_subsingleton.mpr inferInstance), zero_nsmul]
  | succ n ih =>
    let e : (Fin (n + 1) → M) ≃ₗ[R] M × (Fin n → M) :=
      (LinearEquiv.piCongrLeft R (fun _ : Option (Fin n) => M) (finSuccEquiv n)) ≪≫ₗ
        LinearEquiv.piOptionEquivProd R
    rw [ℓ.value_linearEquiv e (powerTorsion_prod hM (powerTorsion_fin _ hM)),
      ℓ.value_prod hM (powerTorsion_fin _ hM), ih, succ_nsmul, add_comm]

end TorsionLength
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechLevel
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.module _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
namespace Lech
universe u
variable {R : Type u} [CommRing R] {I : Ideal R}

lemma powerTorsion_quotient : powerTorsion I (ModuleCat.of R (R ⧸ I)) := by
  refine ⟨1, ?_⟩
  rw [pow_one, Ideal.annihilator_quotient]

end Lech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProductSourceCoverOrdinaryPositive
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option synthInstance.maxHeartbeats 200000
namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.ProductSourceCover
open scoped BigOperators

lemma negativeCount_le {n : ℕ} (m : Fin n → ℤ) : negativeCount m ≤ n := by
  calc negativeCount m ≤ ∑ _i : Fin n,1 := Finset.sum_le_sum (fun i _ => by split_ifs <;> omega)
       _ = n := by simp
lemma single_signed_rank (k : ℤ) :
    (-1:ℤ)^(if k < -1 then 1 else 0)*(k+1).natAbs=k+1 := by
  by_cases hk : k < -1
  · rw [ite_eq_left hk,pow_one,Int.natCast_natAbs,abs_of_neg (by omega)]
    ring
  · rw [ite_eq_right hk,pow_zero,one_mul,Int.natCast_natAbs,abs_of_nonneg (by omega)]
 

lemma signedRank_euler (n : ℕ) (m : Fin n → ℤ) :
    (-1:ℤ)^negativeCount m*(signedRank m:ℤ)=∏ i,(m i+1) := by
  induction n with
  | zero => simp [negativeCount,signedRank]
  | succ n ih =>
    rw [←Fin.cons_self_tail m,negativeCount_cons,signedRank_cons,Fin.prod_univ_succ]
    simp only [Fin.cons_zero,Fin.cons_succ,Nat.cast_mul,pow_add]
    calc _ = ((-1:ℤ)^(if m 0 < -1 then 1 else 0)*(m 0+1).natAbs)*
        ((-1:ℤ)^negativeCount (Fin.tail m)*(signedRank (Fin.tail m):ℤ)) := by ring
         _ = _ := by rw [single_signed_rank,ih]
end Lech.ProductSourceCover


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProductSourceCoverCechNat
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical
namespace Lech.ProductSourceCover


open scoped BigOperators Classical
lemma negativeCount_root (n : ℕ) (r : Fin n → ℤ) (a : ℤ) :
    negativeCount (fun i => a-1-r i)=(Finset.univ.filter (fun i => a < r i)).card := by
  have hi : ∀ i : Fin n,(a-1-r i < -1) ↔ a < r i := fun i => by omega
  simp [negativeCount,hi]
end Lech.ProductSourceCover


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealQuotientFunctor
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.TensorIdeal
open CategoryTheory MonoidalCategory
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

lemma quotient_torsion (M : Type u) [AddCommGroup M] [Module R M] :
    powerTorsion I (ModuleCat.of R (M ⧸ (I • (⊤ : Submodule R M)))) := by
  refine ⟨1,?_⟩
  rw [pow_one]
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    rw [←Submodule.Quotient.mk_smul,Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hr Submodule.mem_top

end Lech.TensorIdeal

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProductSourceCoverRootSigned
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical
namespace Lech.ProductSourceCover
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
open scoped BigOperators
universe u
variable {C : Type u} [CommRing C] (I : Ideal C) (ℓ : TorsionLength I)
variable (n : ℕ) [LinearOrder (Chart n)]
omit [LinearOrder (Chart n)] in
lemma root_signedRank_real (r : Fin n → ℤ) (a : ℤ) :
    (-1:ℝ)^rootDegree n r a*(signedRank (fun j => a-1-r j):ℝ)=∏ j,((a-r j:ℤ):ℝ) := by
  have he := congrArg (fun z : ℤ => (z:ℝ)) (signedRank_euler n (fun j => a-1-r j))
  push_cast at he
  simp only [negativeCount_root] at he
  change (-1:ℝ)^rootDegree n r a*(signedRank (fun j => a-1-r j):ℝ)=_ at he
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.prod_congr rfl
  intro j _
  push_cast
  ring
end Lech.ProductSourceCover


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CechReduction
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.FiniteModuleCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] {ι : Type} [Fintype ι] [LinearOrder ι]
variable (D : Diagram R ι) (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R)

variable (I : Ideal R)


omit [LinearOrder ι] in
lemma reduction_cochains_torsion (q : ℕ) :
    powerTorsion I (ModuleCat.of R (cochains (reduction D I) q)) :=
  (powerTorsion I).prop_of_iso
    (TensorIdeal.quotientPiEquiv I (fun s : Set.powersetCard ι q => D.obj s.val)).toModuleIso
    (TensorIdeal.quotient_torsion I (cochains D q))

lemma reduction_homology_torsion (q : ℕ) :
    powerTorsion I ((complex (reduction D I)).homology q) :=
  powerTorsion_epi I ((complex (reduction D I)).homologyπ q)
    (powerTorsion_mono I ((complex (reduction D I)).iCycles q)
      (reduction_cochains_torsion D I q))

lemma reduction_positiveHomology_torsion (q : ℕ) :
    powerTorsion I ((positiveComplex (reduction D I)).homology q) :=
  powerTorsion_epi I ((positiveComplex (reduction D I)).homologyπ q)
    (powerTorsion_mono I ((positiveComplex (reduction D I)).iCycles q)
      (reduction_cochains_torsion D I (q+1)))

end Lech.FiniteModuleCech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootCechCoefficients
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ProjectiveRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
open ProductSourceCover
open scoped TensorProduct
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]
  (m : Fin n → ℤ) (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [F.Additive]

lemma coefficient_pure (q : ℤ) (hq : q≠negativeCount m+1) :
    IsZero ((coefficientCech R n m F).homology q) :=
  (isZero_single_obj_homology (.up ℤ) (negativeCount m+1) _ q hq).of_iso
    (coefficientHomologyIso R n m F q)

end Lech.ProjectiveRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReducedRootCohomology
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ProjectiveRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex ProductSourceCover
open scoped TensorProduct
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]
  (m : Fin n → ℤ) (I : Ideal R)

lemma reduced_pure (q : ℕ) (hq : q≠negativeCount m+1) :
    IsZero ((reducedCech R n m I).homology q) := by
  apply IsZero.of_iso _ (reducedHomologyIso R n m I q)
  apply coefficient_pure
  exact_mod_cast hq

variable (ell : TorsionLength I)
lemma reduced_length :
    ell.value ((reducedCech R n m I).homology (negativeCount m+1)) =
      signedRank m • ell.value (ModuleCat.of R (R ⧸ I)) :=
  (ell.value_linearEquiv (reducedHomologyEquiv R n m I)
    (powerTorsion_fin _ powerTorsion_quotient)).trans (ell.value_fin powerTorsion_quotient _)

lemma reduced_length_zero (q : ℕ) (hq : q≠negativeCount m+1) :
    ell.value ((reducedCech R n m I).homology q)=0 :=
  ell.zero (reduced_pure R n m I q hq)

end Lech.ProjectiveRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootLayers
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.cechInclusionIter_mono _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j, z j ∈ I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup

variable (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ)

lemma raise_apply (m : Fin n → ℤ) (N : ℕ) (i : Fin n) : raise m N i = m i+N := by
  induction N generalizing m with
  | zero => simp only [raise,Nat.cast_zero,add_zero]
  | succ N ih => rw [raise,ih,Nat.cast_succ]; ring



end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ExceptionalRootCohomology
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ProjectiveRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]
  (m : Fin n → ℤ) (I : Ideal R)

variable (ell : TorsionLength I)
omit [LinearOrder (Chart n)] in
lemma reducedPositive_length_eq (q : ℕ) :
    ell.value ((reducedPositive R n m I).homology q) =
      ell.value ((reducedCech R n m I).homology (q+1)) :=
  ell.eq_of_iso (reducedPositiveHomologyIso R n m I q)
    (FiniteModuleCech.reduction_positiveHomology_torsion _ I q)
    (FiniteModuleCech.reduction_homology_torsion _ I (q+1))

lemma reducedPositive_length :
    ell.value ((reducedPositive R n m I).homology (negativeCount m)) =
      signedRank m • ell.value (ModuleCat.of R (R ⧸ I)) := by
  rw [reducedPositive_length_eq,reduced_length]

lemma reducedPositive_length_zero (q : ℕ) (hq : q≠negativeCount m) :
    ell.value ((reducedPositive R n m I).homology q)=0 := by
  rw [reducedPositive_length_eq,reduced_length_zero R n m I ell (q+1) (by omega)]

end Lech.ProjectiveRoot

namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex ProductSourceCover
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ} [LinearOrder (Chart n)]
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (m : Fin n → ℤ)
  (hgen : Ideal.span (Set.range z)=I) (ell : TorsionLength I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))

include hgen hds hmu ha in
omit [LinearOrder (Chart n)] in
lemma exceptional_length_eq (q : ℕ) :
    ell.value ((exceptionalCech I z hz m).homology q) =
      ell.value ((ProjectiveRoot.reducedPositive R n m I).homology q) :=
  (ell.eq_of_isoModSerre (homologyMap (fibreCechMap I z hz m).positiveComplex q)
    (FiniteModuleCech.reduction_positiveHomology_torsion _ I q)
    (FiniteModuleCech.reduction_positiveHomology_torsion _ I q)
    (fibreCech_homology I z hz m hgen ell hds hmu ha q)).symm

include hgen hds hmu ha in
 
theorem exceptional_length :
    ell.value ((exceptionalCech I z hz m).homology (negativeCount m)) =
      signedRank m • ell.value (ModuleCat.of R (R ⧸ I)) := by
  rw [exceptional_length_eq I z hz m hgen ell hds hmu ha,
    ProjectiveRoot.reducedPositive_length]

include hgen hds hmu ha in
lemma exceptional_length_zero (q : ℕ) (hq : q≠negativeCount m) :
    ell.value ((exceptionalCech I z hz m).homology q)=0 := by
  rw [exceptional_length_eq I z hz m hgen ell hds hmu ha,
    ProjectiveRoot.reducedPositive_length_zero R n m I ell q hq]

omit [LinearOrder (Chart n)] in
lemma exceptional_torsion (q : ℕ) : powerTorsion I ((exceptionalCech I z hz m).homology q) :=
  FiniteModuleCech.reduction_positiveHomology_torsion _ I q

include hgen hds hmu ha in
 
theorem exceptional_root_euler (r : Fin n → ℤ) (a : ℤ) :
    ∑ q ∈ Finset.range (n+1), (-1:ℝ)^q *
      (ell.value ((exceptionalCech I z hz (fun j => a-1-r j)).homology q)).toReal =
        (ell.value (ModuleCat.of R (R ⧸ I))).toReal * ∏ j,((a-r j:ℤ):ℝ) := by
  let m : Fin n → ℤ := fun j => a-1-r j
  have hn : negativeCount m ≤ n := negativeCount_le m
  rw [Finset.sum_eq_single (negativeCount m)]
  · rw [exceptional_length I z hz m hgen ell hds hmu ha,ENNReal.toReal_nsmul]
    simp only [nsmul_eq_mul]
    have he := root_signedRank_real (n:=n) r a
    rw [rootDegree,←negativeCount_root] at he
    change (-1:ℝ)^negativeCount m * ((signedRank m:ℝ) * _) = _
    rw [←mul_assoc,he,mul_comm]
  · intro q hq hneq
    rw [exceptional_length_zero I z hz m hgen ell hds hmu ha q hneq,ENNReal.toReal_zero,mul_zero]
  · intro h
    exact (h (Finset.mem_range.mpr (by omega))).elim

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootGLayerCohomology
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
open ProductSourceCover
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ} [LinearOrder (Chart n)]
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (m : Fin n → ℤ)
  (hgen : Ideal.span (Set.range z)=I) (ell : TorsionLength I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))

omit [LinearOrder (Chart n)] in
lemma exceptionalZ_negative (q : ℤ) (hq : q<0) : IsZero ((exceptionalZ I z hz m).homology q) := by
  apply HomologicalComplex.ExactAt.isZero_homology
  apply HomologicalComplex.extend_exactAt
  intro p hp
  change (p:ℤ)=q at hp
  omega

omit [LinearOrder (Chart n)] in
lemma exceptionalZ_torsion (q : ℤ) : powerTorsion I ((exceptionalZ I z hz m).homology q) := by
  cases q with
  | ofNat q =>
      exact (powerTorsion I).prop_of_iso
        ((exceptionalCech I z hz m).extendHomologyIso ComplexShape.embeddingUpNat (j:=q) rfl).symm
        (exceptional_torsion I z hz m q)
  | negSucc q => exact powerTorsion_zero I (exceptionalZ_negative I z hz m _ (by omega))

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ExceptionalRootEulerZ
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex ProductSourceCover
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ} [LinearOrder (Chart n)]
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (hgen : Ideal.span (Set.range z)=I)
  (ell : TorsionLength I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))

include hgen hds hmu ha in
lemma exceptionalZ_root_euler (r : Fin n → ℤ) (a : ℤ) :
    finiteHomologyEuler ell (exceptionalZ I z hz (fun j=>a-1-r j)) 0 n=
      ell.realValue (ModuleCat.of R (R ⧸ I))*∏ j,((a-r j:ℤ):ℝ) := by
  unfold TorsionLength.realValue
  rw [←exceptional_root_euler I z hz hgen ell hds hmu ha r a]
  unfold finiteHomologyEuler
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  change (ell.value _).toReal=(ell.value _).toReal
  congr 1
  have he := (exceptionalCech I z hz (fun j=>a-1-r j)).extendHomologyIso
    ComplexShape.embeddingUpNat (j:=q) (j':=(0:ℤ)+q) (by simp)
  exact ell.eq_of_iso he (exceptionalZ_torsion I z hz _ _) (exceptional_torsion I z hz _ q)

omit [LinearOrder (Chart n)] in
lemma raise_rootAmbient (s : ℕ) (r : Fin n → ℤ) (j : ℕ) :
    raise (rootAmbient s r 0) j=fun v => (-((n+1)*s:ℕ):ℤ)+j-1-r v := by
  funext v
  simp only [rootAmbient,baseTwist,raise_apply]
  ring

include hgen hds hmu ha in
lemma ambientStrip_euler_oai (s : ℕ) (r : Fin n → ℤ) (N : ℕ) :
    (∑ j∈Finset.range N,finiteHomologyEuler ell
      (exceptionalZ I z hz (raise (rootAmbient s r 0) j)) 0 n)=
        ell.realValue (ModuleCat.of R (R ⧸ I))*rootPrefix n r (n+1) s N := by
  unfold rootPrefix
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [raise_rootAmbient,exceptionalZ_root_euler I z hz hgen ell hds hmu ha]
  congr 1
  apply Finset.prod_congr rfl
  intro v hv
  push_cast
  ring
end Lech.ReesRoot

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.ReesRoot.ambientStrip_euler_oai.{u} := @OAI.Lech.ReesRoot.ambientStrip_euler_oai.{u}
