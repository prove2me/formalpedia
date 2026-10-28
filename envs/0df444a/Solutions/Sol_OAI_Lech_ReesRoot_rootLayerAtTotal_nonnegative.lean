-- Prove2me | solution 1 for OAI.Lech.ReesRoot.rootLayerAtTotal_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T23:33:37.736851+00:00
-- url     : https://prove2.me/submissions/1470c07d-c123-4801-9ccf-1d7c98d5b50c

import Mathlib
import Definitions.Def_OAIQ032L039
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


namespace Lech.ProductSourceCover

section


open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators Classical
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]

omit [LinearOrder (Chart n)] in
lemma rootDegree_nonnegative_layer {s : ℕ} {r : Fin n → ℤ}
    (hr : RootPositions n s r) (i : ℕ) (l : ℤ) (hl : 0 ≤ l) :
    rootDegree n r (l-(i:ℤ)*(s:ℤ)) ≤ i := by
  have hsub : Finset.univ.filter (fun j : Fin n => l-(i:ℤ)*(s:ℤ) < r j) ⊆
      Finset.univ.filter (fun j : Fin n => j.val < i) := by
    intro j hj
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hj ⊢
    by_contra hn
    have ht : (i:ℤ) ≤ (j.val:ℤ)+1 := by omega
    have hm := mul_le_mul_of_nonneg_right ht (show (0:ℤ)≤(s:ℤ) by omega)
    have hp := (hr j).2
    nlinarith
  exact (Finset.card_le_card hsub).trans (by rw [Fin.card_filter_val_lt];exact min_le_right _ _)
end


open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
open scoped BigOperators Classical
universe u
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
lemma exceptional_length_zero (q : ℕ) (hq : q≠negativeCount m) :
    ell.value ((exceptionalCech I z hz m).homology q)=0 := by
  rw [exceptional_length_eq I z hz m hgen ell hds hmu ha,
    ProjectiveRoot.reducedPositive_length_zero R n m I ell q hq]

omit [LinearOrder (Chart n)] in
lemma exceptional_torsion (q : ℕ) : powerTorsion I ((exceptionalCech I z hz m).homology q) :=
  FiniteModuleCech.reduction_positiveHomology_torsion _ I q

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealFilteredComplex
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.module _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.IdealFiltered
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

lemma order_source (h s : ℕ) (i : ℕ) (hi : i ≤ h) : order h s (-(i:ℤ))=(h-i)*s := by
  unfold order
  congr 1
  omega

end Lech.IdealFiltered

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootG
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.cechInclusionIter_mono _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j, z j ∈ I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup

variable (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (m : Fin n → ℤ)



lemma enlarged_twist (i : ℕ) (hi : i ≤ h) :
    raise (baseTwist h s m) (IdealFiltered.order h s (-(i:ℤ))) = fun j => m j-(i*s:ℕ) := by
  funext j
  rw [raise_apply,baseTwist,IdealFiltered.order_source h s i hi,Nat.sub_mul,Nat.cast_sub (Nat.mul_le_mul_right s hi)]
  push_cast
  ring



end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootNilpotence
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Lech.TensorTotal
variable (F : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℕ)
  (H : ∀ k, Homotopy (z k^a • 𝟙 F) 0)

variable (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))



lemma enlargedAt_isZero (m : Fin n → ℤ) (p q : ℤ) (hp : IsZero (F.X p)) :
    IsZero (((enlargedAt I z hz F h s hd m).X p).X q) := by
  let Q := (cechZ I z hz m).X q
  exact @IsZero.of_mono (ModuleCat.{u} R) _ _ _ _
    ((IdealFiltered.ambientInclusion I F h s hd Q).f p)
    (IdealFiltered.ambientInclusion_mono I F h s hd Q p)
    (((CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat.{u} R)).flip.obj Q).map_isZero hp)


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

include hgen hds hmu ha in
lemma exceptionalZ_zero (q : ℤ) (hq : q≠(negativeCount m:ℤ)) :
    ell.zeroClass ((exceptionalZ I z hz m).homology q) := by
  cases q with
  | ofNat q =>
      apply ell.zeroClass.prop_of_iso
        ((exceptionalCech I z hz m).extendHomologyIso ComplexShape.embeddingUpNat (j:=q) rfl).symm
      exact ⟨exceptional_torsion I z hz m q,
        exceptional_length_zero I z hz m hgen ell hds hmu ha q (by
          intro he
          apply hq
          exact congrArg (fun v : ℕ => (v : ℤ)) he)⟩
  | negSucc q => exact ell.zeroClass.prop_of_isZero (exceptionalZ_negative I z hz m _ (by omega))

variable (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (p : ℤ) [Module.Flat R (F.X p)] (b : ℕ) (B : Module.Basis (Fin b) R (F.X p))

omit [LinearOrder (Chart n)] in
include B hgen in
lemma layerAtRow_torsion (q : ℤ) : powerTorsion I (((layerAt I z hz F h s hd m).X p).homology q) :=
  (powerTorsion I).prop_of_iso (layerAtRowHomologyBasisIso I z hz m hgen F h s hd p b B q).symm
    (powerTorsion_fin b (exceptionalZ_torsion I z hz _ q))

omit [LinearOrder (Chart n)] in
include B hgen in
lemma layerAtRow_length (q : ℤ) :
    ell.value (((layerAt I z hz F h s hd m).X p).homology q) =
      b • ell.value ((exceptionalZ I z hz (raise m (IdealFiltered.order h s p))).homology q) :=
  (ell.eq_of_iso (layerAtRowHomologyBasisIso I z hz m hgen F h s hd p b B q)
    (layerAtRow_torsion I z hz m hgen F h s hd p b B q)
    (powerTorsion_fin b (exceptionalZ_torsion I z hz _ q))).trans
      (ell.value_fin (exceptionalZ_torsion I z hz _ q) b)

include B hgen hds hmu ha in
lemma layerAtRow_zero (q : ℤ) (hq : q≠(negativeCount (raise m (IdealFiltered.order h s p)):ℤ)) :
    ell.zeroClass (((layerAt I z hz F h s hd m).X p).homology q) := by
  refine ⟨layerAtRow_torsion I z hz m hgen F h s hd p b B q,?_⟩
  rw [layerAtRow_length I z hz m hgen ell F h s hd p b B q,
    (exceptionalZ_zero I z hz _ hgen ell hds hmu ha q hq).2,smul_zero]
end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootLayerTotal
attribute [-instance] _root_.OAI.Lech.BicomplexTotal.diagonal_additive _root_.OAI.Lech.BicomplexTotal.diagonal_preservesFiniteColimits _root_.OAI.Lech.BicomplexTotal.diagonal_preservesFiniteLimits _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
open ProductSourceCover
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ} [LinearOrder (Chart n)]
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (m : Fin n → ℤ)
  (hgen : Ideal.span (Set.range z)=I) (ell : TorsionLength I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (b : ℤ → ℕ) (B : ∀ p,Module.Basis (Fin (b p)) R (F.X p))
  (hflat : ∀ p,Module.Flat R (F.X p))

omit [LinearOrder (Chart n)] in
lemma layerAt_isZero (p : ℤ) (hp : IsZero (F.X p)) :
    IsZero ((layerAt I z hz F h s hd m).X p) := by
  apply FiniteComplex.isZero_of_X
  intro q
  exact (TensorIdeal.quotientFunctor I).map_isZero (enlargedAt_isZero I z hz F h s hd m p q hp)

omit [LinearOrder (Chart n)] in
lemma rootLayerAt_twist (r : Fin n → ℤ) (l p : ℤ) (hp : -(n+1:ℤ)≤p ∧ p≤0) :
    raise (baseTwist (n+1) s (fun j => l-1-r j)) (IdealFiltered.order (n+1) s p)=
      fun j => (l-((-p).toNat:ℤ)*(s:ℤ))-1-r j := by
  have hi : ((-p).toNat:ℤ) = -p := Int.toNat_of_nonneg (by omega)
  have he : p = -((-p).toNat:ℤ) := by omega
  conv_lhs => rw [he,enlarged_twist (n+1) s _ (-p).toNat (by omega)]
  funext j
  simp only [Nat.cast_mul]
  ring

include hgen hds hmu ha B hflat in
 
theorem rootLayerAtTotal_nonnegative_oai (r : Fin n → ℤ) (hr : RootPositions n s r)
    (hb : ∀ p,p < -(n+1:ℤ) ∨ 0<p → IsZero (F.X p))
    (l : ℤ) (hl : 0≤l) (k : ℤ) (hk : 0<k) :
    ell.zeroClass (((rootLayerAt I z hz F s hd r l).total (.up ℤ)).homology k) := by
  apply BicomplexTotal.devissage ell.zeroClass (-(n+1:ℤ)) (n+2) _ k
  · intro p hp
    exact layerAt_isZero I z hz _ F (n+1) s hd p (hb p (by omega))
  intro p
  apply ell.zeroClass.prop_of_iso (BicomplexTotal.singleHomologyIso _ p k).symm
  by_cases hp : -(n+1:ℤ)≤p ∧ p≤0
  · let := hflat p
    apply layerAtRow_zero I z hz _ hgen ell hds hmu ha F (n+1) s hd p (b p) (B p)
    rw [rootLayerAt_twist s r l p hp,negativeCount_root]
    have hi : ((-p).toNat:ℤ) = -p := Int.toNat_of_nonneg (by omega)
    have hc := rootDegree_nonnegative_layer n hr (-p).toNat l hl
    change (Finset.univ.filter (fun j => l-((-p).toNat:ℤ)*(s:ℤ) < r j)).card≤(-p).toNat at hc
    omega
  · exact ell.zeroClass.prop_of_isZero ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) (-p+k)).map_isZero
      (layerAt_isZero I z hz _ F (n+1) s hd p (hb p (by omega))))

end Lech.ReesRoot

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.ReesRoot.rootLayerAtTotal_nonnegative_oai.{u} := @OAI.Lech.ReesRoot.rootLayerAtTotal_nonnegative_oai.{u}
