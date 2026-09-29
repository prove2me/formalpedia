-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_closure_genericFibre_iso_of_isClosedImmersion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/04a112b6-a5f3-56c2-b314-09694223daa1

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange
import Theorems.Thm_AlgebraicGeometry_flat_image_comp_of_isDedekindDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_closure_genericFibre_iso_of_isClosedImmersion

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_closure_genericFibre_iso_of_isClosedImmersion.GoodReductionJacobian"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.baseChangePointToBase RelativeGroupLaw.baseChangePointToBase_coe RelativeGroupLaw.baseChangePointToBase_mul RelativeGroupLaw.exists_relativeGroupLaw_image_of_homomorphism_baseChange"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "mul_assoc mul_one inv mul baseChangePointToBase baseChangePointToBase_coe baseChange baseChangePointToBase_mul genericFibre fibre exists_relativeGroupLaw_image_of_homomorphism_baseChange"
namespace ClosureDVR
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

open IsDiscreteValuationRing

section GenericPoint

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

theorem isLocalization_away {ϖ : R} (hϖ : Irreducible ϖ) : IsLocalization.Away ϖ K := by
  rw [IsLocalization.Away, isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, n, rfl⟩
    exact (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n hϖ.ne_zero))).isUnit
  · intro z
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) z
    have hb0 : (b : R) ≠ 0 := nonZeroDivisors.ne_zero hb
    obtain ⟨n, u, hu⟩ := eq_unit_mul_pow_irreducible hb0 hϖ
    refine ⟨⟨a * ↑u⁻¹, ⟨ϖ ^ n, n, rfl⟩⟩, ?_⟩
    have hbK : algebraMap R K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    change algebraMap R K a / algebraMap R K b * algebraMap R K (ϖ ^ n) = algebraMap R K (a * ↑u⁻¹)
    rw [div_mul_eq_mul_div, div_eq_iff hbK, ← map_mul, ← map_mul]
    congr 1
    rw [hu, ← _root_.mul_assoc, _root_.mul_assoc a, Units.inv_mul, _root_.mul_one]
  · intro x y h
    exact ⟨1, by rw [IsFractionRing.injective R K h]⟩

scoped instance isOpenImmersion_specGenericFibreInclusion : IsOpenImmersion (specGenericFibreInclusion R K) := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  haveI := isLocalization_away R K hϖ
  exact AlgebraicGeometry.IsOpenImmersion.of_isLocalization ϖ

scoped instance isSchemeTheoreticallyDominant_specGenericFibreInclusion :
    IsSchemeTheoreticallyDominant (specGenericFibreInclusion R K) := by
  haveI : IsDominant (specGenericFibreInclusion R K) := by
    refine ⟨?_⟩
    change DenseRange (PrimeSpectrum.comap (algebraMap R K))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
    intro x hx
    rw [RingHom.mem_ker] at hx
    have : x = 0 := (IsFractionRing.injective R K) (by rw [hx, map_zero])
    simp [this]
  exact IsSchemeTheoreticallyDominant.of_isDominant _

end GenericPoint

end GoodReductionJacobian.RelativeGroupLaw.ClosureDVR
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_closure_genericFibre_iso_of_isClosedImmersion.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_closure_genericFibre_iso_of_isClosedImmersion.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_closure_genericFibre_iso_of_isClosedImmersion.GoodReductionJacobian.RelativeGroupLaw.ClosureDVR"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_closure_genericFibre_iso_of_isClosedImmersion.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_closure_genericFibre_iso_of_isClosedImmersion.GoodReductionJacobian.RelativeGroupLaw"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_closure_genericFibre_iso_of_isClosedImmersion.GoodReductionJacobian"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.baseChangePointToBase RelativeGroupLaw.baseChangePointToBase_coe RelativeGroupLaw.baseChangePointToBase_mul RelativeGroupLaw.exists_relativeGroupLaw_image_of_homomorphism_baseChange"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "mul_assoc mul_one inv mul baseChangePointToBase baseChangePointToBase_coe baseChange baseChangePointToBase_mul genericFibre fibre exists_relativeGroupLaw_image_of_homomorphism_baseChange"
namespace ClosureDVR
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

theorem dominant_toImage {X J : Scheme.{u}} (τ : X ⟶ J) [QuasiCompact τ] : IsSchemeTheoreticallyDominant τ.toImage := by
  rw [isSchemeTheoreticallyDominant_iff]
  let U : J.affineOpens → τ.image.affineOpens := fun V => ⟨τ.imageι ⁻¹ᵁ V.1, V.2.preimage τ.imageι⟩
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top U ?_ ?_
  · rw [← top_le_iff]
    intro b _
    obtain ⟨_, ⟨V, hV, rfl⟩, hbV, -⟩ := J.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (τ.imageι b)) isOpen_univ
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV⟩, hbV⟩
  · intro V
    rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply, ← le_bot_iff]
    intro s hs
    exact (τ.toImage_app_injective V ((RingHom.mem_ker).mp hs |>.trans (map_zero _).symm) : _)

end GoodReductionJacobian.RelativeGroupLaw.ClosureDVR
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_closure_genericFibre_iso_of_isClosedImmersion.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_closure_genericFibre_iso_of_isClosedImmersion.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_closure_genericFibre_iso_of_isClosedImmersion.GoodReductionJacobian.RelativeGroupLaw.ClosureDVR"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_closure_genericFibre_iso_of_isClosedImmersion.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_closure_genericFibre_iso_of_isClosedImmersion.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_closure_genericFibre_iso_of_isClosedImmersion.GoodReductionJacobian.RelativeGroupLaw.ClosureDVR"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_closure_genericFibre_iso_of_isClosedImmersion.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_closure_genericFibre_iso_of_isClosedImmersion.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_closure_genericFibre_iso_of_isClosedImmersion.GoodReductionJacobian.RelativeGroupLaw.ClosureDVR"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.baseChangePointToBase RelativeGroupLaw.baseChangePointToBase_coe RelativeGroupLaw.baseChangePointToBase_mul RelativeGroupLaw.exists_relativeGroupLaw_image_of_homomorphism_baseChange"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "mul_assoc mul_one inv mul baseChangePointToBase baseChangePointToBase_coe baseChange baseChangePointToBase_mul genericFibre fibre exists_relativeGroupLaw_image_of_homomorphism_baseChange"
namespace ClosureDVR
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

section Closure

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} [IsSeparated f]
  {BK : Scheme.{u}} {gK : BK ⟶ Spec (CommRingCat.of K)} [IsReduced BK]
  (iK : SchemeHomOver gK (pullback.snd f (specGenericFibreInclusion R K))) [IsClosedImmersion iK.1]

noncomputable abbrev σ : BK ⟶ J := iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)

theorem σ_comp : σ K iK ≫ f = gK ≫ specGenericFibreInclusion R K := by
  rw [Category.assoc, pullback.condition, ← Category.assoc, iK.2]

noncomputable abbrev NK : Scheme.{u} := pullback ((σ K iK).imageι ≫ f) (specGenericFibreInclusion R K)

noncomputable def jK : NK K iK ⟶ pullback f (specGenericFibreInclusion R K) :=
  pullback.map ((σ K iK).imageι ≫ f) (specGenericFibreInclusion R K) f (specGenericFibreInclusion R K)
    (σ K iK).imageι (𝟙 _) (𝟙 _) (Category.comp_id _) (by rw [Category.comp_id, Category.id_comp])

noncomputable def eInv : BK ⟶ NK K iK :=
  pullback.lift (σ K iK).toImage gK (by rw [Scheme.Hom.toImage_imageι_assoc, σ_comp])

@[scoped simp] theorem eInv_fst : eInv K iK ≫ pullback.fst _ _ = (σ K iK).toImage := pullback.lift_fst _ _ _
@[scoped simp] theorem eInv_snd : eInv K iK ≫ pullback.snd _ _ = gK := pullback.lift_snd _ _ _

theorem eInv_jK : eInv K iK ≫ jK K iK = iK.1 := by
  apply pullback.hom_ext
  · rw [Category.assoc, jK, pullback.lift_fst, ← Category.assoc, eInv_fst, Scheme.Hom.toImage_imageι]
  · rw [Category.assoc, jK, pullback.lift_snd, ← Category.assoc, eInv_snd, Category.comp_id]
    exact iK.2.symm

scoped instance : IsClosedImmersion (eInv K iK) := by
  have h1 : IsClosedImmersion (eInv K iK ≫ jK K iK) := by rw [eInv_jK]; infer_instance
  have h2 : IsSeparated (jK K iK ≫ pullback.snd f (specGenericFibreInclusion R K)) := by
    rw [jK, pullback.lift_snd, Category.comp_id]; infer_instance
  haveI : IsSeparated (jK K iK) := IsSeparated.of_comp (jK K iK) (pullback.snd f (specGenericFibreInclusion R K))
  exact IsClosedImmersion.of_comp (eInv K iK) (jK K iK)

theorem isReduced_image : IsReduced (σ K iK).image := by
  haveI := dominant_toImage (σ K iK)
  exact IsSchemeTheoreticallyDominant.isReduced (σ K iK).toImage

scoped instance : IsReduced (NK K iK) := by
  haveI := isReduced_image K iK
  exact isReduced_of_isOpenImmersion (pullback.fst ((σ K iK).imageι ≫ f) (specGenericFibreInclusion R K))

scoped instance : Surjective (eInv K iK) := by
  haveI := dominant_toImage (σ K iK)
  haveI : IsDominant (σ K iK).toImage := inferInstance
  refine ⟨fun p => ?_⟩
  by_contra hp
  push_neg at hp

  let φ := pullback.fst ((σ K iK).imageι ≫ f) (specGenericFibreInclusion R K)
  have hC : IsClosed (Set.range (eInv K iK)) := (eInv K iK).isClosedEmbedding.isClosed_range
  have hV : IsOpen (φ '' (Set.range (eInv K iK))ᶜ) := φ.isOpenEmbedding.isOpenMap _ hC.isOpen_compl
  have hne : (φ '' (Set.range (eInv K iK))ᶜ).Nonempty := ⟨φ p, p, fun ⟨b, hb⟩ => hp b hb, rfl⟩
  obtain ⟨_, ⟨q, hq, rfl⟩, b, hb⟩ := (σ K iK).toImage.denseRange.inter_open_nonempty _ hV hne
  apply hq
  refine ⟨b, φ.isOpenEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, eInv_fst]; exact hb

scoped instance : IsIso (eInv K iK) := isIso_of_isClosedImmersion_of_surjective _

noncomputable def ePt : SchemeHomOver (pullback.snd ((σ K iK).imageι ≫ f) (specGenericFibreInclusion R K)) gK :=
  ⟨CategoryTheory.inv (eInv K iK), by rw [IsIso.inv_comp_eq, eInv_snd]⟩

theorem ePt_coe : (ePt K iK).1 = CategoryTheory.inv (eInv K iK) := rfl

theorem ePt_iK : (ePt K iK).1 ≫ iK.1 = jK K iK := by
  rw [ePt_coe, IsIso.inv_comp_eq, eInv_jK]

end Closure
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_closure_genericFibre_iso_of_isClosedImmersion.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_closure_genericFibre_iso_of_isClosedImmersion.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_closure_genericFibre_iso_of_isClosedImmersion.GoodReductionJacobian.RelativeGroupLaw.ClosureDVR"

section Main

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} [IsSeparated f] (L : RelativeGroupLaw R f)
  {BK : Scheme.{u}} {gK : BK ⟶ Spec (CommRingCat.of K)} [IsReduced BK] (LBK : RelativeGroupLaw K gK)
  (iK : SchemeHomOver gK (pullback.snd f (specGenericFibreInclusion R K))) [IsClosedImmersion iK.1]
  (hiK : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t gK),
      NeronModelInfra.schemeHomOverComp (LBK.mul t x y) iK =
        (L.genericFibre K).mul t (NeronModelInfra.schemeHomOverComp x iK) (NeronModelInfra.schemeHomOverComp y iK))

noncomputable def Φ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (z : SchemeHomOver t (pullback.snd ((σ K iK).imageι ≫ f) (specGenericFibreInclusion R K))) :
    SchemeHomOver (t ≫ specGenericFibreInclusion R K) f :=
  NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion R K) z)
    (⟨(σ K iK).imageι, rfl⟩ : SchemeHomOver ((σ K iK).imageι ≫ f) f)

theorem Φ_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (z : SchemeHomOver t (pullback.snd ((σ K iK).imageι ≫ f) (specGenericFibreInclusion R K))) :
    (Φ K iK z).1 = z.1 ≫ pullback.fst _ _ ≫ (σ K iK).imageι := by
  rw [Φ, NeronModelInfra.schemeHomOverComp_coe, RelativeGroupLaw.baseChangePointToBase_coe, Category.assoc]

theorem Φ_injective {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} :
    Function.Injective (Φ K iK (T := T) (t := t)) := by
  intro z w h
  have h' := congrArg Subtype.val h
  rw [Φ_coe, Φ_coe, ← Category.assoc, ← Category.assoc] at h'
  have h'' := (cancel_mono (σ K iK).imageι).mp h'
  exact Subtype.ext ((cancel_mono (pullback.fst ((σ K iK).imageι ≫ f) (specGenericFibreInclusion R K))).mp h'')

theorem Φ_comp_eInv {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} (a : SchemeHomOver t gK) :
    Φ K iK (NeronModelInfra.schemeHomOverComp a (⟨eInv K iK, eInv_snd K iK⟩ : SchemeHomOver gK _)) =
      RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion R K) (NeronModelInfra.schemeHomOverComp a iK) := by
  apply Subtype.ext
  rw [Φ_coe, NeronModelInfra.schemeHomOverComp_coe, RelativeGroupLaw.baseChangePointToBase_coe,
    NeronModelInfra.schemeHomOverComp_coe, Category.assoc, Category.assoc, ← Category.assoc (eInv K iK), eInv_fst,
    Scheme.Hom.toImage_imageι]

variable (LN : RelativeGroupLaw R ((σ K iK).imageι ≫ f))
  (hLN : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t ((σ K iK).imageι ≫ f)),
    NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨(σ K iK).imageι, rfl⟩ : SchemeHomOver ((σ K iK).imageι ≫ f) f) =
      L.mul t (NeronModelInfra.schemeHomOverComp x ⟨(σ K iK).imageι, rfl⟩) (NeronModelInfra.schemeHomOverComp y ⟨(σ K iK).imageι, rfl⟩))

include hLN in
theorem Φ_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (z w : SchemeHomOver t (pullback.snd ((σ K iK).imageι ≫ f) (specGenericFibreInclusion R K))) :
    Φ K iK ((LN.genericFibre K).mul t z w) = L.mul _ (Φ K iK z) (Φ K iK w) := by
  change NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion R K)
      ((LN.baseChange (specGenericFibreInclusion R K)).mul t z w)) _ = _
  rw [RelativeGroupLaw.baseChangePointToBase_mul, hLN]
  rfl

include hiK hLN in

theorem eInv_hom {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (a b : SchemeHomOver t gK) :
    NeronModelInfra.schemeHomOverComp (LBK.mul t a b) (⟨eInv K iK, eInv_snd K iK⟩ : SchemeHomOver gK _) =
      (LN.genericFibre K).mul t (NeronModelInfra.schemeHomOverComp a ⟨eInv K iK, eInv_snd K iK⟩)
        (NeronModelInfra.schemeHomOverComp b ⟨eInv K iK, eInv_snd K iK⟩) := by
  apply Φ_injective K iK
  rw [Φ_comp_eInv, hiK, Φ_mul K L iK LN hLN, Φ_comp_eInv, Φ_comp_eInv]
  change RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion R K)
      ((L.baseChange (specGenericFibreInclusion R K)).mul t _ _) = _
  rw [RelativeGroupLaw.baseChangePointToBase_mul]

include hiK hLN in

theorem ePt_hom {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t (pullback.snd ((σ K iK).imageι ≫ f) (specGenericFibreInclusion R K))) :
    NeronModelInfra.schemeHomOverComp ((LN.genericFibre K).mul t x y) (ePt K iK) =
      LBK.mul t (NeronModelInfra.schemeHomOverComp x (ePt K iK)) (NeronModelInfra.schemeHomOverComp y (ePt K iK)) := by
  have hxe : ∀ z : SchemeHomOver t (pullback.snd ((σ K iK).imageι ≫ f) (specGenericFibreInclusion R K)),
      NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp z (ePt K iK))
        (⟨eInv K iK, eInv_snd K iK⟩ : SchemeHomOver gK _) = z := fun z =>
    Subtype.ext (by
      rw [NeronModelInfra.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe, ePt_coe, Category.assoc,
        IsIso.inv_hom_id, Category.comp_id])
  have hee : ∀ c : SchemeHomOver t gK,
      NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp c (⟨eInv K iK, eInv_snd K iK⟩ : SchemeHomOver gK _))
        (ePt K iK) = c := fun c =>
    Subtype.ext (by
      rw [NeronModelInfra.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe, ePt_coe, Category.assoc,
        IsIso.hom_inv_id, Category.comp_id])
  have h := eInv_hom K L LBK iK hiK LN hLN t (NeronModelInfra.schemeHomOverComp x (ePt K iK)) (NeronModelInfra.schemeHomOverComp y (ePt K iK))
  rw [hxe, hxe] at h
  rw [← h, hee]

end Main
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_closure_genericFibre_iso_of_isClosedImmersion.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_closure_genericFibre_iso_of_isClosedImmersion.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_closure_genericFibre_iso_of_isClosedImmersion.GoodReductionJacobian.RelativeGroupLaw.ClosureDVR"

end GoodReductionJacobian.RelativeGroupLaw.ClosureDVR
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_closure_genericFibre_iso_of_isClosedImmersion.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_closure_genericFibre_iso_of_isClosedImmersion.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_closure_genericFibre_iso_of_isClosedImmersion.GoodReductionJacobian.RelativeGroupLaw.ClosureDVR"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_closure_genericFibre_iso_of_isClosedImmersion.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_closure_genericFibre_iso_of_isClosedImmersion.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_closure_genericFibre_iso_of_isClosedImmersion.GoodReductionJacobian.RelativeGroupLaw.ClosureDVR"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_closure_genericFibre_iso_of_isClosedImmersion.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_closure_genericFibre_iso_of_isClosedImmersion.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_closure_genericFibre_iso_of_isClosedImmersion.GoodReductionJacobian.RelativeGroupLaw.ClosureDVR"

open GoodReductionJacobian.RelativeGroupLaw.ClosureDVR in

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} [IsSeparated f] (L : RelativeGroupLaw R f)
    {BK : Scheme.{u}} {gK : BK ⟶ Spec (CommRingCat.of K)} [IsReduced BK] (LBK : RelativeGroupLaw K gK)
    (iK : SchemeHomOver gK (pullback.snd f (specGenericFibreInclusion R K)))
    (hci : IsClosedImmersion iK.1)
    (hiK : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t gK),
      NeronModelInfra.schemeHomOverComp (LBK.mul t x y) iK =
        (L.genericFibre K).mul t (NeronModelInfra.schemeHomOverComp x iK) (NeronModelInfra.schemeHomOverComp y iK)) :
    ∃ (LN : RelativeGroupLaw R ((iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)).imageι ≫ f))
      (e : SchemeHomOver
        (pullback.snd ((iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)).imageι ≫ f) (specGenericFibreInclusion R K)) gK),
      Flat ((iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)).imageι ≫ f) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
          (x y : SchemeHomOver t ((iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)).imageι ≫ f)),
        NeronModelInfra.schemeHomOverComp (LN.mul t x y)
            (⟨(iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)).imageι, rfl⟩ :
              SchemeHomOver ((iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)).imageι ≫ f) f) =
          L.mul t (NeronModelInfra.schemeHomOverComp x ⟨(iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)).imageι, rfl⟩)
            (NeronModelInfra.schemeHomOverComp y ⟨(iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)).imageι, rfl⟩)) ∧
      ((∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), L.mul t x y = L.mul t y x) →
        ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
          (x y : SchemeHomOver t ((iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)).imageι ≫ f)),
        LN.mul t x y = LN.mul t y x) ∧
      IsIso e.1 ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
          (x y : SchemeHomOver t
            (pullback.snd ((iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)).imageι ≫ f) (specGenericFibreInclusion R K))),
        NeronModelInfra.schemeHomOverComp ((LN.genericFibre K).mul t x y) e =
          LBK.mul t (NeronModelInfra.schemeHomOverComp x e) (NeronModelInfra.schemeHomOverComp y e)) ∧
      e.1 ≫ iK.1 =
        pullback.map ((iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)).imageι ≫ f) (specGenericFibreInclusion R K)
          f (specGenericFibreInclusion R K) (iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)).imageι (𝟙 _) (𝟙 _)
          (Category.comp_id _) (by rw [Category.comp_id, Category.id_comp]) := by
  haveI := hci
  have hflat : Flat (σ K iK ≫ f) := by rw [σ_comp]; infer_instance
  haveI : Flat ((σ K iK).imageι ≫ f) := AlgebraicGeometry.flat_image_comp_of_isDedekindDomain (σ K iK) f
  obtain ⟨LN, hLN, hLNcomm⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_image_of_homomorphism_baseChange
      (specGenericFibreInclusion R K) L LBK iK hiK
  exact ⟨LN, ePt K iK, inferInstance, hLN, fun hcomm _ t x y => hLNcomm hcomm t x y, (inferInstance : IsIso (CategoryTheory.inv (eInv K iK))),
    fun t x y => ePt_hom K L LBK iK hiK LN hLN t x y, ePt_iK K iK⟩

end S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_closure_genericFibre_iso_of_isClosedImmersion
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_closure_genericFibre_iso_of_isClosedImmersion (solution)
