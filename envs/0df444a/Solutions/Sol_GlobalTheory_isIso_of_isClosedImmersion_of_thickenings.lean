-- Prove2me | solution 1 for GlobalTheory.isIso_of_isClosedImmersion_of_thickenings
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:26:41.499798+00:00
-- url     : https://prove2.me/submissions/42619d21-0d80-4133-8b1a-792ad7038c43

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasicOpenEqZeroOfMemIInfPowSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoOfIsClosedImmersionOfThickenings
import Theorems.Thm_GlobalTheory_ThickeningClosed_isOpen_zeroLocusOpen
import Theorems.Thm_GlobalTheory_ThickeningClosed_exists_mul_eq_zero_of_mem
import Theorems.Thm_GlobalTheory_ThickeningClosed_mem_of_thickenings
import Theorems.Thm_GlobalTheory_ThickeningClosed_noZeroDivisors_fiber
import Theorems.Thm_GlobalTheory_eq_zero_of_flat_of_forall_fiber
import Theorems.Thm_GlobalTheory_localizedModule_mk_one_eq_zero_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ →
      ∀ (H : Over (Spec (CommRingCat.of R))) [Flat H.hom] [LocallyOfFiniteType H.hom]
        (_e : 𝟙_ _ ⟶ H), (∀ p, IsIntegral (H.hom.fiber p)) →
        ∀ (Z : Scheme.{0}) (ι : Z ⟶ H.left) [IsClosedImmersion ι],
          (∀ n : ℕ, ∃ l : (_root_.ReciprocityTheory.ChartRestriction.G.Out.thickObj R I n H).left ⟶ Z, l ≫ ι = (_root_.ReciprocityTheory.ChartRestriction.G.Out.fstG I n H).left) →
            IsIso ι := by
  intro R _ _ I hI H _ _ e hfib Z ι _ hth
  rw [IsClosedImmersion.isIso_iff_ker_eq_bot]
  have hpre : ∀ U : H.left.affineOpens,
      Spec.map (Spec.preimage (U.2.fromSpec ≫ H.hom)) = U.2.fromSpec ≫ H.hom :=
    fun U ↦ Spec.map_preimage _
  have hft : ∀ U : H.left.affineOpens, (Spec.preimage (U.2.fromSpec ≫ H.hom)).hom.FiniteType := by
    intro U
    haveI := U.2.isOpenImmersion_fromSpec
    have : LocallyOfFiniteType (Spec.map (Spec.preimage (U.2.fromSpec ≫ H.hom))) := by
      rw [hpre]; infer_instance
    exact HasRingHomProperty.Spec_iff.mp this
  have hfl : ∀ U : H.left.affineOpens, (Spec.preimage (U.2.fromSpec ≫ H.hom)).hom.Flat := by
    intro U
    haveI := U.2.isOpenImmersion_fromSpec
    rw [← Flat.SpecMap_iff, hpre]; infer_instance
  haveI : IsLocallyNoetherian H.left := ⟨fun U ↦ by
    letI := (Spec.preimage (U.2.fromSpec ≫ H.hom)).hom.toAlgebra
    haveI : Algebra.FiniteType R Γ(H.left, U) := hft U
    exact Algebra.FiniteType.isNoetherianRing R _⟩
  have hsec : ∀ s : Spec (CommRingCat.of R), H.hom (e.left s) = s := by
    intro s
    have hw := Over.w e
    have : (e.left ≫ H.hom) s = s := by rw [hw]; rfl
    exact this
  have hqU : ∀ (U : H.left.affineOpens) (q : PrimeSpectrum Γ(H.left, U)), U.2.fromSpec q ∈ U.1 := by
    intro U q
    have : U.2.fromSpec q ∈ Set.range U.2.fromSpec := ⟨q, rfl⟩
    rwa [U.2.range_fromSpec] at this
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top (fun U : H.left.affineOpens ↦ U)
    (iSup_affineOpens_eq_top _) fun U ↦ ?_
  refine eq_bot_iff.mpr fun a ha ↦ ?_
  show a = 0
  letI : Algebra R Γ(H.left, U) := (Spec.preimage (U.2.fromSpec ≫ H.hom)).hom.toAlgebra
  haveI : Module.Flat R Γ(H.left, U) := hfl U
  haveI : IsNoetherianRing Γ(H.left, U) := IsLocallyNoetherian.component_noetherian U
  haveI := U.2.isOpenImmersion_fromSpec
  have hj : Spec.map (CommRingCat.ofHom (algebraMap R Γ(H.left, U))) = U.2.fromSpec ≫ H.hom :=
    hpre U
  have hpt : ∀ q : PrimeSpectrum Γ(H.left, U),
      Ideal.under R q.asIdeal = (H.hom (U.2.fromSpec q)).asIdeal := by
    intro q
    have : Spec.map (CommRingCat.ofHom (algebraMap R Γ(H.left, U))) q = H.hom (U.2.fromSpec q) := by
      rw [hj]; rfl
    rw [← this]; rfl
  refine _root_.GlobalTheory.eq_zero_of_flat_of_forall_fiber (A := R) (B := Γ(H.left, U))
    (L := Γ(H.left, U))
    (fun p _ ↦ haveI := hfib p; _root_.GlobalTheory.ThickeningClosed.noZeroDivisors_fiber H.hom U.2.fromSpec hj p)
    (fun q _ ↦ ?_)
  obtain ⟨m, hm, hPm⟩ := Ideal.exists_le_maximal _ (H.hom (U.2.fromSpec q)).2.ne_top
  let M : Spec (CommRingCat.of R) := ⟨m, hm.isPrime⟩
  have hIM : I ≤ (H.hom (e.left M)).asIdeal := by
    rw [hsec]; exact hI.trans (sInf_le ⟨bot_le, hm⟩)
  have hy := _root_.GlobalTheory.ThickeningClosed.mem_of_thickenings I H.hom ι hth (e.left M) hIM
  have hPM : H.hom (U.2.fromSpec q) ⤳ H.hom (e.left M) := by
    rw [hsec]; exact (PrimeSpectrum.le_iff_specializes _ M).mp hPm
  obtain ⟨y', hy'y, hy'P⟩ := Flat.generalizingMap H.hom hPM
  have hy'Z := hy'y.mem_open (_root_.GlobalTheory.ThickeningClosed.isOpen_zeroLocusOpen _) hy
  haveI := hfib (H.hom (U.2.fromSpec q))
  have hirr : IsIrreducible (H.hom ⁻¹' {H.hom (U.2.fromSpec q)}) := by
    rw [← Scheme.Hom.range_fiberι, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (H.hom.fiberι _).continuous.continuousOn
  obtain ⟨z, hzP, hzZ, hzU⟩ := hirr.2 _ _ (_root_.GlobalTheory.ThickeningClosed.isOpen_zeroLocusOpen _) U.1.isOpen
    ⟨y', hy'P, hy'Z⟩ ⟨U.2.fromSpec q, rfl, hqU U q⟩
  have hq'z : U.2.fromSpec (U.2.primeIdealOf ⟨z, hzU⟩) = z := U.2.fromSpec_primeIdealOf ⟨z, hzU⟩
  refine ⟨U.2.primeIdealOf ⟨z, hzU⟩, ?_, ?_⟩
  · rw [hpt, hpt, hq'z]
    exact congrArg PrimeSpectrum.asIdeal hzP
  · rw [_root_.GlobalTheory.localizedModule_mk_one_eq_zero_iff]
    exact _root_.GlobalTheory.ThickeningClosed.exists_mul_eq_zero_of_mem ι.ker U _ (by rw [hq'z]; exact hzZ) ha
end _root_.GlobalTheory
end GlobalTheory
