-- Prove2me | solution 1 for OAI.Lech.ReesRoot.layerAtTotal_finite
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T23:32:32.011048+00:00
-- url     : https://prove2.me/submissions/66e41e1d-2b55-4d3c-b51f-c300393aebc8

import Mathlib
import Definitions.Def_OAIQ032L039
import Theorems.Thm_OAI_Lech_ReesRoot_exceptionalZ_finite

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
-- module Solutions.OAIQ032_LECH.Multiplicity_ExceptionalRootCohomology
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
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (m : Fin n → ℤ)
  (hgen : Ideal.span (Set.range z)=I) (ell : TorsionLength I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))

omit [LinearOrder (Chart n)] in
lemma exceptional_torsion (q : ℕ) : powerTorsion I ((exceptionalCech I z hz m).homology q) :=
  FiniteModuleCech.reduction_positiveHomology_torsion _ I q

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
lemma layerAtRow_finite (q : ℤ) : ell.finiteClass (((layerAt I z hz F h s hd m).X p).homology q) := by
  refine ⟨layerAtRow_torsion I z hz m hgen F h s hd p b B q,?_⟩
  rw [layerAtRow_length I z hz m hgen ell F h s hd p b B q,nsmul_eq_mul]
  exact ENNReal.mul_ne_top (by simp) (exceptionalZ_finite I z hz _ hgen ell hds hmu ha q).2

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

include hgen hds hmu ha B hflat in
lemma layerAtTotal_finite_oai (hb : ∀ p,p < -(h:ℤ) ∨ 0<p → IsZero (F.X p)) (k : ℤ) :
    ell.finiteClass (((layerAt I z hz F h s hd m).total (.up ℤ)).homology k) := by
  apply BicomplexTotal.devissage ell.finiteClass (-(h:ℤ)) (h+1) _ k
  · intro p hp
    exact layerAt_isZero I z hz m F h s hd p (hb p (by omega))
  intro p
  apply ell.finiteClass.prop_of_iso (BicomplexTotal.singleHomologyIso _ p k).symm
  let := hflat p
  exact layerAtRow_finite I z hz m hgen ell hds hmu ha F h s hd p (b p) (B p) (-p+k)


end Lech.ReesRoot

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.ReesRoot.layerAtTotal_finite_oai.{u} := @OAI.Lech.ReesRoot.layerAtTotal_finite_oai.{u}
