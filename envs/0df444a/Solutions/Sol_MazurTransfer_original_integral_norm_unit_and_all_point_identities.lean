-- Prove2me | solution 1 for MazurTransfer.original_integral_norm_unit_and_all_point_identities
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T05:22:37.420058+00:00
-- url     : https://prove2.me/submissions/ca9d40b5-c0c7-4aec-91d5-b15367ef9363

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the same chosen integral norm extension preserves the identity point over every original integral test scheme, using the same original generic-density descent and local group law.
Named downstream consumer: same actual integral norm-kernel Hopf group laws.
-/
import Definitions.Def_MazurTransfer_OriginalPicardComparisonGroupProvidersData20261020
import Definitions.Def_MazurTransfer_Order13GoodPrimeLocalGenericGroupConstructorData
import Definitions.Def_MazurTransfer_Order13GoodPrimeIntegralNormExtensionsData
import Theorems.Thm_MazurTransfer_Order13GoodPrimeGenericNormUnit_localGenericNorm_preserves_unit
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open MazurTransfer.Order13GoodPrimeLocalGenericGroupIdentity MazurTransfer.Order13GoodPrimeLocalGenericPicardComparison
open MazurTransfer.Order13GoodPrimeGenericNormUnit MazurTransfer.Order13GoodPrimeIntegralNormExtensions
open MazurTransfer.Order13GoodPrimeLocalPicardModels MazurTransfer.Order13LocalIntegralCoefficientMaps
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison.actualGroup
namespace MazurTransfer.OriginalIntegralNormUnitAndAllPointIdentitiesBoundary20261020
end MazurTransfer.OriginalIntegralNormUnitAndAllPointIdentitiesBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: descend zero preservation of the SAME generic norm to
its already selected integral extension. The generic-density argument
uses the pinned FLT generic-fibre restriction proof.
Named downstream consumer: actual integral norm group morphisms.
-/

noncomputable section
namespace MazurTransfer.OriginalIntegralNormUnitProof20261020
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open Order13GoodPrimeLocalGenericGroupIdentity Order13GoodPrimeLocalGenericPicardComparison
open Order13GoodPrimeGenericNormUnit Order13GoodPrimeIntegralNormExtensions
open Order13GoodPrimeLocalPicardModels Order13LocalIntegralCoefficientMaps
open Order13ActualPicardDiamondSchemeEndomorphism Order13SameIntegralPicardRationalSchemeComparison
open scoped CategoryTheory.MonObj
variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)

theorem localGenericInclusion_dominant : IsDominant (specGenericFibreInclusion (LocalRing q) ℚ) := by
  rw [isDominant_iff, specGenericFibreInclusion]
  have hker : RingHom.ker (algebraMap (LocalRing q) ℚ) ≤ nilradical (LocalRing q) := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective (LocalRing q) ℚ)]
    exact bot_le
  have hd := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical
    (algebraMap (LocalRing q) ℚ)).mpr hker
  simp at hd ⊢
  exact hd

theorem integralNorm_preserves_unit
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] :
    NeronModelInfra.schemeHomOverComp ((localLaw q hq).one (𝟙 _))
      (integralNorm q hq φ) = (localLaw q hq).one (𝟙 _) := by
  letI := (localPicard_geometry q hq).2.1
  letI := localGenericInclusion_dominant q
  have h := localGenericNorm_preserves_unit q hq φ
  rw [← integralNorm_restrict q hq φ] at h
  have hb := congrArg (RelativeGroupLaw.baseChangePointToBase
    (specGenericFibreInclusion (LocalRing q) ℚ)) h
  dsimp only [genericLocalLaw] at hb
  change RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion (LocalRing q) ℚ)
    (NeronModelInfra.schemeHomOverComp
      (((localLaw q hq).baseChange (specGenericFibreInclusion (LocalRing q) ℚ)).one (𝟙 _))
      (genericFibreRestrict (LocalRing q) ℚ (localPicard q hq).toBase
        (localPicard q hq).toBase (integralNorm q hq φ))) = _ at hb
  rw [RelativeGroupLaw.baseChangePointToBase_comp_genericFibreRestrict,
    RelativeGroupLaw.baseChangePointToBase_one] at hb
  have hn := congrArg Subtype.val ((localLaw q hq).one_natural
    (𝟙 _) (𝟙 _ ≫ specGenericFibreInclusion (LocalRing q) ℚ)
    (𝟙 _ ≫ specGenericFibreInclusion (LocalRing q) ℚ) (by simp))
  change (𝟙 _ ≫ specGenericFibreInclusion (LocalRing q) ℚ) ≫
    ((localLaw q hq).one (𝟙 _)).val =
      ((localLaw q hq).one (𝟙 _ ≫ specGenericFibreInclusion (LocalRing q) ℚ)).val at hn
  have hb' := congrArg Subtype.val hb
  change ((localLaw q hq).one (𝟙 _ ≫ specGenericFibreInclusion (LocalRing q) ℚ)).val ≫
    (integralNorm q hq φ).val =
      ((localLaw q hq).one (𝟙 _ ≫ specGenericFibreInclusion (LocalRing q) ℚ)).val at hb'
  rw [← hn] at hb'
  apply Subtype.ext
  apply ext_of_isDominant_of_isSeparated (localPicard q hq).toBase
    (by simp only [NeronModelInfra.schemeHomOverComp_coe, Category.assoc,
      (integralNorm q hq φ).property, ((localLaw q hq).one (𝟙 _)).property])
    (specGenericFibreInclusion (LocalRing q) ℚ)
  simpa only [NeronModelInfra.schemeHomOverComp_coe, Category.assoc, Category.id_comp] using hb'

end MazurTransfer.OriginalIntegralNormUnitProof20261020

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: zero preservation for the SAME integral norm extension
holds on points over every test scheme by naturality of the local law.
Named downstream consumer: the accepted public pointwise group-morphism
contract for actual integral norm morphisms.
-/

noncomputable section
namespace MazurTransfer.OriginalIntegralNormAllPointIdentitiesProof20261020
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open MazurTransfer.OriginalIntegralNormUnitProof20261020 Order13GoodPrimeIntegralNormExtensions
open Order13GoodPrimeLocalPicardModels Order13LocalIntegralCoefficientMaps
open Order13ActualPicardDiamondSchemeEndomorphism Order13SameIntegralPicardRationalSchemeComparison
open scoped CategoryTheory.MonObj
variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)

theorem integralNorm_preserves_all_units
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (LocalRing q))) :
    NeronModelInfra.schemeHomOverComp ((localLaw q hq).one t) (integralNorm q hq φ) =
      (localLaw q hq).one t := by
  have h := congrArg Subtype.val (integralNorm_preserves_unit q hq φ)
  change ((localLaw q hq).one (𝟙 _)).val ≫ (integralNorm q hq φ).val =
    ((localLaw q hq).one (𝟙 _)).val at h
  have hn := congrArg Subtype.val ((localLaw q hq).one_natural (𝟙 _) t t (by simp))
  change t ≫ ((localLaw q hq).one (𝟙 _)).val = ((localLaw q hq).one t).val at hn
  apply Subtype.ext
  change ((localLaw q hq).one t).val ≫ (integralNorm q hq φ).val =
    ((localLaw q hq).one t).val
  rw [← hn, Category.assoc, h]

end MazurTransfer.OriginalIntegralNormAllPointIdentitiesProof20261020

theorem solution : (∀ (q : ℕ) [Fact q.Prime] , IsDominant (specGenericFibreInclusion (LocalRing q) ℚ)) ∧ (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) , ∀ (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ],
NeronModelInfra.schemeHomOverComp ((localLaw q hq).one (𝟙 _))
      (integralNorm q hq φ) = (localLaw q hq).one (𝟙 _)) ∧ (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) , ∀ (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (LocalRing q))),
NeronModelInfra.schemeHomOverComp ((localLaw q hq).one t) (integralNorm q hq φ) =
      (localLaw q hq).one t) := by
  exact ⟨MazurTransfer.OriginalIntegralNormUnitProof20261020.localGenericInclusion_dominant, MazurTransfer.OriginalIntegralNormUnitProof20261020.integralNorm_preserves_unit, MazurTransfer.OriginalIntegralNormAllPointIdentitiesProof20261020.integralNorm_preserves_all_units⟩
#print axioms solution
