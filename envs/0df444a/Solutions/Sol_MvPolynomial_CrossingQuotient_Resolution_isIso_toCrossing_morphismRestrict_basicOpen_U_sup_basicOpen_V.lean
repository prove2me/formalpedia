-- Prove2me | solution 1 for MvPolynomial.CrossingQuotient.Resolution.isIso_toCrossing_morphismRestrict_basicOpen_U_sup_basicOpen_V
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/66018a0b-03ba-5a28-a1e4-9cc5ecfe84d4

import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_CrossingQuotient_Resolution_isIso_toCrossing_morphismRestrict_basicOpen_U_sup_basicOpen_V

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial MvPolynomial.CrossingQuotient

namespace CrossingResolutionL6UV

variable {W : Type u} [CommRing W] (t : W) {e : ℕ} (he : 0 < e)

open MvPolynomial.CrossingQuotient.GlueIndex MvPolynomial.CrossingQuotient.Resolution

local notation "B" => CrossingQuotient W (t ^ e)
local notation "C₀" => CrossingQuotient W t
local notation "uB" => (U (t ^ e) : CrossingQuotient W (t ^ e))
local notation "vB" => (V (t ^ e) : CrossingQuotient W (t ^ e))
local notation "Bu" => Localization.Away (U (t ^ e) : CrossingQuotient W (t ^ e))
local notation "Bv" => Localization.Away (V (t ^ e) : CrossingQuotient W (t ^ e))
local notation "Cx" => Localization.Away (U t : CrossingQuotient W t)
local notation "Cy" => Localization.Away (V t : CrossingQuotient W t)

theorem mk_C_eq (s w : W) : mk s (C w) = algebraMap W (CrossingQuotient W s) w := by
  change mk s (algebraMap W (MvPolynomial (Fin 2) W) w) = _
  exact AlgHom.commutes _ w

abbrev last : Fin e := ⟨e - 1, Nat.sub_lt he Nat.one_pos⟩

section PartU

noncomputable def ψU : B →ₐ[W] Cx :=
  (IsScalarTower.toAlgHom W C₀ Cx).comp (resolutionChart t e ⟨0, he⟩)

theorem ψU_U : ψU t he uB = algebraMap C₀ Cx (U t) := by
  rw [ψU, AlgHom.comp_apply, resolutionChart_U, IsScalarTower.coe_toAlgHom', map_mul,
    ← IsScalarTower.algebraMap_apply]
  change algebraMap W Cx (t ^ 0) * _ = _
  rw [pow_zero, map_one, one_mul]

theorem ψU_V : ψU t he vB = algebraMap W Cx (t ^ (e - 1)) * algebraMap C₀ Cx (V t) := by
  rw [ψU, AlgHom.comp_apply, resolutionChart_V, IsScalarTower.coe_toAlgHom', map_mul,
    ← IsScalarTower.algebraMap_apply]
  rfl

noncomputable abbrev uBinv : Bu := IsLocalization.Away.invSelf (S := Bu) uB

theorem u_mul_uBinv : algebraMap B Bu uB * uBinv t = 1 := IsLocalization.Away.mul_invSelf _

theorem isUnit_ψU_uB : IsUnit ((ψU t he).toRingHom uB) := by
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ψU_U]
  exact IsLocalization.Away.algebraMap_isUnit (U t)

noncomputable def FU : Bu →+* Cx :=
  IsLocalization.Away.lift (S := Bu) uB (g := (ψU t he).toRingHom) (isUnit_ψU_uB t he)

theorem FU_algebraMap (b : B) : FU t he (algebraMap B Bu b) = ψU t he b :=
  IsLocalization.Away.lift_eq (S := Bu) uB (isUnit_ψU_uB t he) b

theorem FU_algebraMap_W (w : W) : FU t he (algebraMap W Bu w) = algebraMap W Cx w := by
  rw [IsScalarTower.algebraMap_apply W B Bu, FU_algebraMap, AlgHom.commutes]

noncomputable def GU₀ : C₀ →ₐ[W] Bu :=
  CrossingQuotient.lift t (algebraMap B Bu uB) (algebraMap W Bu t * uBinv t) (by
    rw [mul_left_comm, u_mul_uBinv, mul_one])

noncomputable def GU : Cx →+* Bu :=
  IsLocalization.Away.lift (S := Cx) (U t) (g := (GU₀ (e := e) t).toRingHom)
    (by
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, GU₀, lift_U]
      exact IsLocalization.Away.algebraMap_isUnit uB)

theorem GU_algebraMap (c : C₀) : GU (e := e) t (algebraMap C₀ Cx c) = GU₀ (e := e) t c :=
  IsLocalization.Away.lift_eq (S := Cx) (U t) _ c

theorem GU_algebraMap_W (w : W) : GU (e := e) t (algebraMap W Cx w) = algebraMap W Bu w := by
  rw [IsScalarTower.algebraMap_apply W C₀ Cx, GU_algebraMap, AlgHom.commutes]

theorem algebraMap_vB : algebraMap B Bu vB = algebraMap W Bu (t ^ e) * uBinv t := by
  calc algebraMap B Bu vB = algebraMap B Bu vB * (algebraMap B Bu uB * uBinv t) := by
          rw [u_mul_uBinv, mul_one]
    _ = algebraMap B Bu (uB * vB) * uBinv t := by rw [map_mul]; ring
    _ = algebraMap W Bu (t ^ e) * uBinv t := by
          rw [U_mul_V, ← IsScalarTower.algebraMap_apply]

theorem GU_comp_FU : (GU (e := e) t).comp (FU t he) = RingHom.id Bu := by
  apply IsLocalization.ringHom_ext (Submonoid.powers uB)
  rw [RingHom.comp_assoc, FU, IsLocalization.Away.lift_comp, RingHom.id_comp]
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro w
    show GU (e := e) t (ψU t he (mk _ (C w))) = algebraMap B Bu (mk _ (C w))
    rw [mk_C_eq, AlgHom.commutes, GU_algebraMap_W, IsScalarTower.algebraMap_apply W B Bu]
  · intro j
    fin_cases j
    · show GU (e := e) t (ψU t he uB) = algebraMap B Bu uB
      rw [ψU_U, GU_algebraMap, GU₀, lift_U]
    · show GU (e := e) t (ψU t he vB) = algebraMap B Bu vB
      rw [ψU_V, map_mul, GU_algebraMap_W, GU_algebraMap, GU₀, lift_V, algebraMap_vB,
        ← mul_assoc, ← map_mul, ← pow_succ, Nat.sub_add_cancel he]

noncomputable abbrev xinv : Cx := IsLocalization.Away.invSelf (S := Cx) (U t)

theorem x_mul_xinv : algebraMap C₀ Cx (U t) * xinv t = 1 := IsLocalization.Away.mul_invSelf _

theorem xinv_mul_x : xinv t * algebraMap C₀ Cx (U t) = 1 := by
  rw [mul_comm (xinv t)]; exact x_mul_xinv t

theorem FU_uBinv : FU t he (uBinv t) = xinv t := by
  have h1 : algebraMap C₀ Cx (U t) * FU t he (uBinv t) = 1 := by
    rw [← ψU_U t he, ← FU_algebraMap, ← map_mul, u_mul_uBinv, map_one]
  exact eq_of_mul_eq_one_of_mul_eq_one h1 (xinv_mul_x t)

theorem algebraMap_t_mul_xinv : algebraMap W Cx t * xinv t = algebraMap C₀ Cx (V t) := by
  rw [IsScalarTower.algebraMap_apply W C₀ Cx, ← U_mul_V, map_mul, mul_right_comm, x_mul_xinv,
    one_mul]

theorem FU_comp_GU : (FU t he).comp (GU (e := e) t) = RingHom.id Cx := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (U t))
  rw [RingHom.comp_assoc, GU, IsLocalization.Away.lift_comp, RingHom.id_comp]
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro w
    show FU t he (GU₀ (e := e) t (mk _ (C w))) = algebraMap C₀ Cx (mk _ (C w))
    rw [mk_C_eq, AlgHom.commutes, FU_algebraMap_W, IsScalarTower.algebraMap_apply W C₀ Cx]
  · intro j
    fin_cases j
    · show FU t he (GU₀ (e := e) t (U t)) = algebraMap C₀ Cx (U t)
      rw [GU₀, lift_U, FU_algebraMap, ψU_U]
    · show FU t he (GU₀ (e := e) t (V t)) = algebraMap C₀ Cx (V t)
      rw [GU₀, lift_V, map_mul, FU_algebraMap_W, FU_uBinv, algebraMap_t_mul_xinv]

noncomputable def ΘU : Bu ≃+* Cx :=
  RingEquiv.ofRingHom (FU t he) (GU (e := e) t) (FU_comp_GU t he) (GU_comp_FU t he)

theorem ΘU_comp_algebraMap : (ΘU t he).toRingHom.comp (algebraMap B Bu) = (ψU t he).toRingHom :=
  IsLocalization.Away.lift_comp (S := Bu) uB (isUnit_ψU_uB t he)

noncomputable abbrev locX : Spec (CommRingCat.of Cx) ⟶ chartScheme t :=
  Spec.map (CommRingCat.ofHom (algebraMap C₀ Cx))

scoped instance isOpenImmersion_locX : IsOpenImmersion (locX t) :=
  IsOpenImmersion.of_isLocalization (U t)

theorem range_locX : Set.range (locX t) =
    ((PrimeSpectrum.basicOpen (U t) : TopologicalSpace.Opens (PrimeSpectrum C₀)) :
      Set (PrimeSpectrum C₀)) :=
  PrimeSpectrum.localization_away_comap_range Cx (U t)

noncomputable abbrev gU : Spec (CommRingCat.of Cx) ⟶ crossingScheme (t ^ e) :=
  Spec.map (CommRingCat.ofHom (ψU t he).toRingHom)

theorem locX_ι_toCrossing : locX t ≫ ι t e ⟨0, he⟩ ≫ toCrossing t e = gU t he := by
  rw [ι_toCrossing, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem gU_eq : gU t he = Spec.map (CommRingCat.ofHom (ΘU t he).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap B Bu)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ΘU_comp_algebraMap]

theorem isIso_ofHom_ΘU : IsIso (CommRingCat.ofHom (ΘU t he).toRingHom) :=
  inferInstanceAs (IsIso (ΘU t he).toCommRingCatIso.hom)

scoped instance isOpenImmersion_gU : IsOpenImmersion (gU t he) := by
  have := isIso_ofHom_ΘU t he
  rw [gU_eq]
  infer_instance

theorem range_gU : Set.range (gU t he) =
    ((PrimeSpectrum.basicOpen uB : TopologicalSpace.Opens (PrimeSpectrum B)) :
      Set (PrimeSpectrum B)) := by
  have := isIso_ofHom_ΘU t he
  rw [gU_eq, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr (Scheme.Hom.surjective _), Set.image_univ]
  exact PrimeSpectrum.localization_away_comap_range Bu uB

theorem image_basicOpen_U :
    ι t e ⟨0, he⟩ ''ᵁ PrimeSpectrum.basicOpen (U t) = toCrossing t e ⁻¹ᵁ PrimeSpectrum.basicOpen uB := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y ∈ Set.range (locX t) := by rw [range_locX]; exact hy
    obtain ⟨z, rfl⟩ := hy'
    change toCrossing t e (ι t e ⟨0, he⟩ (locX t z)) ∈ PrimeSpectrum.basicOpen uB
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, locX_ι_toCrossing]
    have hz : gU t he z ∈ Set.range (gU t he) := ⟨z, rfl⟩
    rw [range_gU] at hz
    exact hz
  · intro hx
    change toCrossing t e x ∈ PrimeSpectrum.basicOpen uB at hx
    obtain ⟨i, y, rfl⟩ := exists_ι_apply_eq t e x
    rw [← Scheme.Hom.comp_apply, ι_toCrossing] at hx
    change uB ∉ Ideal.comap (resolutionChart t e i).toRingHom y.asIdeal at hx
    rw [Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, resolutionChart_U] at hx
    have hU : U t ∉ y.asIdeal := fun h => hx (Ideal.mul_mem_left _ _ h)
    by_cases hi : (i : ℕ) = 0
    · obtain rfl : i = ⟨0, he⟩ := Fin.ext hi
      exact ⟨y, hU, rfl⟩
    ·
      have ht : algebraMap W C₀ t ∉ y.asIdeal := by
        intro h
        apply hx
        apply Ideal.mul_mem_right
        rw [show (i : ℕ) = ((i : ℕ) - 1) + 1 by omega, pow_succ, map_mul]
        exact Ideal.mul_mem_left _ _ h
      rw [← U_mul_V] at ht
      have hV : V t ∉ y.asIdeal := fun h => ht (Ideal.mul_mem_left _ _ h)
      obtain ⟨z, rfl⟩ := mem_range_torusToChart t hU hV i
      refine ⟨torusToChart t (0 : ℕ) z, ?_, ?_⟩
      · change U t ∉ Ideal.comap (torusChart t 0).toRingHom z.asIdeal
        rw [Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, torusChart_U, pow_zero,
          mul_one]
        intro h
        exact z.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h
          (IsUnit.of_mul_eq_one _ (by
            change xT t * (yT t * tinv t) = 1
            rw [← mul_assoc, xT_mul_yT, tT_mul_tinv])))
      · change (torusToChart t ((⟨0, he⟩ : Fin e) : ℕ) ≫ ι t e ⟨0, he⟩) z = (torusToChart t i ≫ ι t e i) z
        rw [torusToChart_ι t e ⟨0, he⟩, torusToChart_ι t e i]

include he in
theorem isIso_morphismRestrict_U :
    IsIso (toCrossing t e ∣_ PrimeSpectrum.basicOpen uB) := by
  set D : (crossingScheme (t ^ e)).Opens := PrimeSpectrum.basicOpen uB with hD
  have hrange₁ : Set.range (locX t ≫ ι t e ⟨0, he⟩) = Set.range (toCrossing t e ⁻¹ᵁ D).ι := by
    rw [Scheme.Opens.range_ι, ← image_basicOpen_U, Scheme.Hom.coe_image, Scheme.Hom.comp_base,
      TopCat.coe_comp, Set.range_comp, range_locX]
    rfl
  have hrange₂ : Set.range (gU t he) = Set.range D.ι := by
    rw [Scheme.Opens.range_ι, range_gU]; rfl
  let φ := IsOpenImmersion.isoOfRangeEq (locX t ≫ ι t e ⟨0, he⟩) (toCrossing t e ⁻¹ᵁ D).ι hrange₁
  let χ := IsOpenImmersion.isoOfRangeEq (gU t he) D.ι hrange₂
  have key : toCrossing t e ∣_ D = φ.inv ≫ χ.hom := by
    rw [← cancel_mono D.ι, morphismRestrict_ι, Category.assoc,
      IsOpenImmersion.isoOfRangeEq_hom_fac, ← locX_ι_toCrossing, ← Category.assoc (locX t),
      ← Category.assoc, IsOpenImmersion.isoOfRangeEq_inv_fac]
  rw [key]
  infer_instance

end PartU

section PartV

noncomputable def ψV : B →ₐ[W] Cy :=
  (IsScalarTower.toAlgHom W C₀ Cy).comp (resolutionChart t e (last he))

theorem ψV_V : ψV t he vB = algebraMap C₀ Cy (V t) := by
  rw [ψV, AlgHom.comp_apply, resolutionChart_V, IsScalarTower.coe_toAlgHom', map_mul,
    ← IsScalarTower.algebraMap_apply]
  change algebraMap W Cy (t ^ (e - 1 - (e - 1))) * _ = _
  rw [Nat.sub_self, pow_zero, map_one, one_mul]

theorem ψV_U : ψV t he uB = algebraMap W Cy (t ^ (e - 1)) * algebraMap C₀ Cy (U t) := by
  rw [ψV, AlgHom.comp_apply, resolutionChart_U, IsScalarTower.coe_toAlgHom', map_mul,
    ← IsScalarTower.algebraMap_apply]

noncomputable abbrev vBinv : Bv := IsLocalization.Away.invSelf (S := Bv) vB

theorem v_mul_vBinv : algebraMap B Bv vB * vBinv t = 1 := IsLocalization.Away.mul_invSelf _

theorem isUnit_ψV_vB : IsUnit ((ψV t he).toRingHom vB) := by
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ψV_V]
  exact IsLocalization.Away.algebraMap_isUnit (V t)

noncomputable def FV : Bv →+* Cy :=
  IsLocalization.Away.lift (S := Bv) vB (g := (ψV t he).toRingHom) (isUnit_ψV_vB t he)

theorem FV_algebraMap (b : B) : FV t he (algebraMap B Bv b) = ψV t he b :=
  IsLocalization.Away.lift_eq (S := Bv) vB (isUnit_ψV_vB t he) b

theorem FV_algebraMap_W (w : W) : FV t he (algebraMap W Bv w) = algebraMap W Cy w := by
  rw [IsScalarTower.algebraMap_apply W B Bv, FV_algebraMap, AlgHom.commutes]

noncomputable def GV₀ : C₀ →ₐ[W] Bv :=
  CrossingQuotient.lift t (algebraMap W Bv t * vBinv t) (algebraMap B Bv vB) (by
    rw [mul_assoc, mul_comm (vBinv t), v_mul_vBinv, mul_one])

noncomputable def GV : Cy →+* Bv :=
  IsLocalization.Away.lift (S := Cy) (V t) (g := (GV₀ (e := e) t).toRingHom)
    (by
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, GV₀, lift_V]
      exact IsLocalization.Away.algebraMap_isUnit vB)

theorem GV_algebraMap (c : C₀) : GV (e := e) t (algebraMap C₀ Cy c) = GV₀ (e := e) t c :=
  IsLocalization.Away.lift_eq (S := Cy) (V t) _ c

theorem GV_algebraMap_W (w : W) : GV (e := e) t (algebraMap W Cy w) = algebraMap W Bv w := by
  rw [IsScalarTower.algebraMap_apply W C₀ Cy, GV_algebraMap, AlgHom.commutes]

theorem algebraMap_uB : algebraMap B Bv uB = algebraMap W Bv (t ^ e) * vBinv t := by
  calc algebraMap B Bv uB = algebraMap B Bv uB * (algebraMap B Bv vB * vBinv t) := by
          rw [v_mul_vBinv, mul_one]
    _ = algebraMap B Bv (uB * vB) * vBinv t := by rw [map_mul]; ring
    _ = algebraMap W Bv (t ^ e) * vBinv t := by
          rw [U_mul_V, ← IsScalarTower.algebraMap_apply]

theorem GV_comp_FV : (GV (e := e) t).comp (FV t he) = RingHom.id Bv := by
  apply IsLocalization.ringHom_ext (Submonoid.powers vB)
  rw [RingHom.comp_assoc, FV, IsLocalization.Away.lift_comp, RingHom.id_comp]
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro w
    show GV (e := e) t (ψV t he (mk _ (C w))) = algebraMap B Bv (mk _ (C w))
    rw [mk_C_eq, AlgHom.commutes, GV_algebraMap_W, IsScalarTower.algebraMap_apply W B Bv]
  · intro j
    fin_cases j
    · show GV (e := e) t (ψV t he uB) = algebraMap B Bv uB
      rw [ψV_U, map_mul, GV_algebraMap_W, GV_algebraMap, GV₀, lift_U, algebraMap_uB,
        ← mul_assoc, ← map_mul, ← pow_succ, Nat.sub_add_cancel he]
    · show GV (e := e) t (ψV t he vB) = algebraMap B Bv vB
      rw [ψV_V, GV_algebraMap, GV₀, lift_V]

noncomputable abbrev yinv : Cy := IsLocalization.Away.invSelf (S := Cy) (V t)

theorem y_mul_yinv : algebraMap C₀ Cy (V t) * yinv t = 1 := IsLocalization.Away.mul_invSelf _

theorem yinv_mul_y : yinv t * algebraMap C₀ Cy (V t) = 1 := by
  rw [mul_comm (yinv t)]; exact y_mul_yinv t

theorem FV_vBinv : FV t he (vBinv t) = yinv t := by
  have h1 : algebraMap C₀ Cy (V t) * FV t he (vBinv t) = 1 := by
    rw [← ψV_V t he, ← FV_algebraMap, ← map_mul, v_mul_vBinv, map_one]
  exact eq_of_mul_eq_one_of_mul_eq_one h1 (yinv_mul_y t)

theorem algebraMap_t_mul_yinv : algebraMap W Cy t * yinv t = algebraMap C₀ Cy (U t) := by
  rw [IsScalarTower.algebraMap_apply W C₀ Cy, ← U_mul_V, map_mul, mul_assoc, y_mul_yinv, mul_one]

theorem FV_comp_GV : (FV t he).comp (GV (e := e) t) = RingHom.id Cy := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (V t))
  rw [RingHom.comp_assoc, GV, IsLocalization.Away.lift_comp, RingHom.id_comp]
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro w
    show FV t he (GV₀ (e := e) t (mk _ (C w))) = algebraMap C₀ Cy (mk _ (C w))
    rw [mk_C_eq, AlgHom.commutes, FV_algebraMap_W, IsScalarTower.algebraMap_apply W C₀ Cy]
  · intro j
    fin_cases j
    · show FV t he (GV₀ (e := e) t (U t)) = algebraMap C₀ Cy (U t)
      rw [GV₀, lift_U, map_mul, FV_algebraMap_W, FV_vBinv, algebraMap_t_mul_yinv]
    · show FV t he (GV₀ (e := e) t (V t)) = algebraMap C₀ Cy (V t)
      rw [GV₀, lift_V, FV_algebraMap, ψV_V]

noncomputable def ΘV : Bv ≃+* Cy :=
  RingEquiv.ofRingHom (FV t he) (GV (e := e) t) (FV_comp_GV t he) (GV_comp_FV t he)

theorem ΘV_comp_algebraMap : (ΘV t he).toRingHom.comp (algebraMap B Bv) = (ψV t he).toRingHom :=
  IsLocalization.Away.lift_comp (S := Bv) vB (isUnit_ψV_vB t he)

noncomputable abbrev locY : Spec (CommRingCat.of Cy) ⟶ chartScheme t :=
  Spec.map (CommRingCat.ofHom (algebraMap C₀ Cy))

scoped instance isOpenImmersion_locY : IsOpenImmersion (locY t) :=
  IsOpenImmersion.of_isLocalization (V t)

theorem range_locY : Set.range (locY t) =
    ((PrimeSpectrum.basicOpen (V t) : TopologicalSpace.Opens (PrimeSpectrum C₀)) :
      Set (PrimeSpectrum C₀)) :=
  PrimeSpectrum.localization_away_comap_range Cy (V t)

noncomputable abbrev gV : Spec (CommRingCat.of Cy) ⟶ crossingScheme (t ^ e) :=
  Spec.map (CommRingCat.ofHom (ψV t he).toRingHom)

theorem locY_ι_toCrossing : locY t ≫ ι t e (last he) ≫ toCrossing t e = gV t he := by
  rw [ι_toCrossing, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem gV_eq : gV t he = Spec.map (CommRingCat.ofHom (ΘV t he).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap B Bv)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ΘV_comp_algebraMap]

theorem isIso_ofHom_ΘV : IsIso (CommRingCat.ofHom (ΘV t he).toRingHom) :=
  inferInstanceAs (IsIso (ΘV t he).toCommRingCatIso.hom)

scoped instance isOpenImmersion_gV : IsOpenImmersion (gV t he) := by
  have := isIso_ofHom_ΘV t he
  rw [gV_eq]
  infer_instance

theorem range_gV : Set.range (gV t he) =
    ((PrimeSpectrum.basicOpen vB : TopologicalSpace.Opens (PrimeSpectrum B)) :
      Set (PrimeSpectrum B)) := by
  have := isIso_ofHom_ΘV t he
  rw [gV_eq, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr (Scheme.Hom.surjective _), Set.image_univ]
  exact PrimeSpectrum.localization_away_comap_range Bv vB

theorem image_basicOpen_V :
    ι t e (last he) ''ᵁ PrimeSpectrum.basicOpen (V t) =
      toCrossing t e ⁻¹ᵁ PrimeSpectrum.basicOpen vB := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y ∈ Set.range (locY t) := by rw [range_locY]; exact hy
    obtain ⟨z, rfl⟩ := hy'
    change toCrossing t e (ι t e (last he) (locY t z)) ∈ PrimeSpectrum.basicOpen vB
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, locY_ι_toCrossing]
    have hz : gV t he z ∈ Set.range (gV t he) := ⟨z, rfl⟩
    rw [range_gV] at hz
    exact hz
  · intro hx
    change toCrossing t e x ∈ PrimeSpectrum.basicOpen vB at hx
    obtain ⟨i, y, rfl⟩ := exists_ι_apply_eq t e x
    rw [← Scheme.Hom.comp_apply, ι_toCrossing] at hx
    change vB ∉ Ideal.comap (resolutionChart t e i).toRingHom y.asIdeal at hx
    rw [Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, resolutionChart_V] at hx
    have hV : V t ∉ y.asIdeal := fun h => hx (Ideal.mul_mem_left _ _ h)
    by_cases hi : (i : ℕ) = e - 1
    · obtain rfl : i = last he := Fin.ext hi
      exact ⟨y, hV, rfl⟩
    · have ht : algebraMap W C₀ t ∉ y.asIdeal := by
        intro h
        apply hx
        apply Ideal.mul_mem_right
        rw [show e - 1 - (i : ℕ) = (e - 1 - (i : ℕ) - 1) + 1 by have := i.2; omega, pow_succ, map_mul]
        exact Ideal.mul_mem_left _ _ h
      rw [← U_mul_V] at ht
      have hU : U t ∉ y.asIdeal := fun h => ht (Ideal.mul_mem_right _ _ h)
      obtain ⟨z, rfl⟩ := mem_range_torusToChart t hU hV i
      refine ⟨torusToChart t (e - 1 : ℕ) z, ?_, ?_⟩
      · change V t ∉ Ideal.comap (torusChart t (e - 1)).toRingHom z.asIdeal
        rw [Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, torusChart_V]
        intro h
        exact z.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h
          ((IsUnit.of_mul_eq_one _ (by
            change yT t * (xT t * tinv t) = 1
            rw [mul_left_comm, ← mul_assoc, xT_mul_yT, tT_mul_tinv])).mul
            ((isUnit_tT t).pow _)))
      · change (torusToChart t ((last he : Fin e) : ℕ) ≫ ι t e (last he)) z = (torusToChart t i ≫ ι t e i) z
        rw [torusToChart_ι t e (last he), torusToChart_ι t e i]

include he in
theorem isIso_morphismRestrict_V :
    IsIso (toCrossing t e ∣_ PrimeSpectrum.basicOpen vB) := by
  set D : (crossingScheme (t ^ e)).Opens := PrimeSpectrum.basicOpen vB with hD
  have hrange₁ : Set.range (locY t ≫ ι t e (last he)) = Set.range (toCrossing t e ⁻¹ᵁ D).ι := by
    rw [Scheme.Opens.range_ι, ← image_basicOpen_V, Scheme.Hom.coe_image, Scheme.Hom.comp_base,
      TopCat.coe_comp, Set.range_comp, range_locY]
    rfl
  have hrange₂ : Set.range (gV t he) = Set.range D.ι := by
    rw [Scheme.Opens.range_ι, range_gV]; rfl
  let φ := IsOpenImmersion.isoOfRangeEq (locY t ≫ ι t e (last he)) (toCrossing t e ⁻¹ᵁ D).ι hrange₁
  let χ := IsOpenImmersion.isoOfRangeEq (gV t he) D.ι hrange₂
  have key : toCrossing t e ∣_ D = φ.inv ≫ χ.hom := by
    rw [← cancel_mono D.ι, morphismRestrict_ι, Category.assoc,
      IsOpenImmersion.isoOfRangeEq_hom_fac, ← locY_ι_toCrossing, ← Category.assoc (locY t),
      ← Category.assoc, IsOpenImmersion.isoOfRangeEq_inv_fac]
  rw [key]
  infer_instance

end PartV

include he in
theorem isIso_morphismRestrict_sup :
    IsIso (toCrossing t e ∣_ (PrimeSpectrum.basicOpen uB ⊔ PrimeSpectrum.basicOpen vB)) := by
  set DU : (crossingScheme (t ^ e)).Opens := PrimeSpectrum.basicOpen uB with hDU
  set DV : (crossingScheme (t ^ e)).Opens := PrimeSpectrum.basicOpen vB with hDV
  set S : (crossingScheme (t ^ e)).Opens := DU ⊔ DV with hS

  let Dfam : Bool → (crossingScheme (t ^ e)).Opens := fun b => if b then DU else DV
  have hle : ∀ b, Dfam b ≤ S := by
    intro b; cases b
    · exact le_sup_right
    · exact le_sup_left
  have hiso : ∀ b, IsIso (toCrossing t e ∣_ Dfam b) := by
    intro b; cases b
    · exact isIso_morphismRestrict_V t he
    · exact isIso_morphismRestrict_U t he

  have hcov : (⨆ b, S.ι ⁻¹ᵁ Dfam b) = ⊤ := by
    apply S.ι.image_injective
    change S.ι ''ᵁ (⨆ b, S.ι ⁻¹ᵁ Dfam b) = S.ι ''ᵁ ⊤
    rw [Scheme.Hom.image_iSup, Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
    apply le_antisymm
    · exact iSup_le fun b => (Scheme.Hom.image_preimage_eq_opensRange_inf S.ι (Dfam b)).le.trans
        (inf_le_left.trans (Scheme.Opens.opensRange_ι S).le)
    · change DU ⊔ DV ≤ _
      apply sup_le
      · refine le_trans ?_ (le_iSup _ true)
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
        exact le_inf le_sup_left le_rfl
      · refine le_trans ?_ (le_iSup _ false)
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
        exact le_inf le_sup_right le_rfl
  change MorphismProperty.isomorphisms Scheme (toCrossing t e ∣_ S)
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (U := fun b => S.ι ⁻¹ᵁ Dfam b) hcov]
  intro b
  have heq : S.ι ''ᵁ (S.ι ⁻¹ᵁ Dfam b) = Dfam b := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr (hle b)
  rw [(MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict (toCrossing t e) S (S.ι ⁻¹ᵁ Dfam b) ≪≫ morphismRestrictEq _ heq)]
  exact hiso b

end CrossingResolutionL6UV
p2m_reactivate "P2MW.S_MvPolynomial_CrossingQuotient_Resolution_isIso_toCrossing_morphismRestrict_basicOpen_U_sup_basicOpen_V.CrossingResolutionL6UV"

open AlgebraicGeometry MvPolynomial MvPolynomial.CrossingQuotient in
theorem solution
    {W : Type u} [CommRing W] (t : W) {e : ℕ} (he : 0 < e) :
    Resolution.ι t e ⟨0, he⟩ ''ᵁ PrimeSpectrum.basicOpen (U t) =
        Resolution.toCrossing t e ⁻¹ᵁ PrimeSpectrum.basicOpen (U (t ^ e)) ∧
      Resolution.ι t e ⟨e - 1, Nat.sub_lt he Nat.one_pos⟩ ''ᵁ PrimeSpectrum.basicOpen (V t) =
        Resolution.toCrossing t e ⁻¹ᵁ PrimeSpectrum.basicOpen (V (t ^ e)) ∧
      IsIso (Resolution.toCrossing t e ∣_ PrimeSpectrum.basicOpen (U (t ^ e))) ∧
      IsIso (Resolution.toCrossing t e ∣_ PrimeSpectrum.basicOpen (V (t ^ e))) ∧
      IsIso (Resolution.toCrossing t e ∣_
        (PrimeSpectrum.basicOpen (U (t ^ e)) ⊔ PrimeSpectrum.basicOpen (V (t ^ e)))) :=
  ⟨CrossingResolutionL6UV.image_basicOpen_U t he, CrossingResolutionL6UV.image_basicOpen_V t he,
    CrossingResolutionL6UV.isIso_morphismRestrict_U t he,
    CrossingResolutionL6UV.isIso_morphismRestrict_V t he,
    CrossingResolutionL6UV.isIso_morphismRestrict_sup t he⟩

end S_MvPolynomial_CrossingQuotient_Resolution_isIso_toCrossing_morphismRestrict_basicOpen_U_sup_basicOpen_V
end P2MW
export P2MW.S_MvPolynomial_CrossingQuotient_Resolution_isIso_toCrossing_morphismRestrict_basicOpen_U_sup_basicOpen_V (solution)
