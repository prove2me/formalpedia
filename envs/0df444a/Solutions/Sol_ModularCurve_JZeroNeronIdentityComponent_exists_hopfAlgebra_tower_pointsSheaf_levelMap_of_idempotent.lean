-- Prove2me | solution 1 for ModularCurve.JZeroNeronIdentityComponent.exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/e0a4dbd8-d43c-53b5-88c8-932b04a171d7

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronIdentityComponent
import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_schemeKer_forall_mem_torsionSubset_iff
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_idempotent
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_algEquiv_globalSections_of_isAffineHom
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_bialgHom_of_schemeHomOver_of_forall_mul
import Theorems.Thm_AlgebraicGeometry_IsSeparated_eq_of_spec_map_subtype_comp_eq
import Theorems.Thm_AlgebraicGeometry_moduleFinite_globalSections_of_isProper_of_isAffineHom
import Theorems.Thm_AlgebraicGeometry_exists_algEquiv_globalSections_pullback_spec_tensorProduct
import Theorems.Thm_HopfAlgebra_exists_sheaf_smallFppfTopology_specInt_sectionsEquiv_algHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace FltWs11
namespace RoadB
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in

noncomputable abbrev ιK (p q : ℕ) [Fact p.Prime] (N : ModularCurve.JZeroNeronIdentityComponent p) (m : ℕ) : N.L.schemeKer (q ^ m) ⟶ N.G :=
  pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1
end FltWs11.RoadB

namespace FltWs11
namespace RoadB
namespace SecA

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra ModularCurve

local notation "ℤS" => Spec (CommRingCat.of ℤ)
local notation "Qb" => AlgebraicClosure ℚ
local notation "NMIcomp" => NeronModelInfra.schemeHomOverComp
local notation "tQ" => Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))

variable {p : ℕ} [Fact p.Prime] (N : JZeroNeronIdentityComponent p)
  {Am : Scheme.{0}} (ι : Am ⟶ N.G) {E : Scheme.{0}} (j : E ⟶ Am)
  {H : Type} [CommRing H] [HopfAlgebra ℤ H]
  (ePts : ∀ (T : Type) [CommRing T] [Algebra ℤ T],
    WithConv (H →ₐ[ℤ] T) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ T))) (j ≫ ι ≫ N.g))

noncomputable def gp (φ : WithConv (H →ₐ[ℤ] Qb)) : JZero p :=
  N.pts.symm (NMIcomp (NMIcomp (ePts Qb φ) (⟨j, rfl⟩ : SchemeHomOver (j ≫ ι ≫ N.g) (ι ≫ N.g)))
    (⟨ι, rfl⟩ : SchemeHomOver (ι ≫ N.g) N.g))

theorem pts_gp (φ : WithConv (H →ₐ[ℤ] Qb)) :
    N.pts (gp N ι j ePts φ) = NMIcomp (NMIcomp (ePts Qb φ) (⟨j, rfl⟩ : SchemeHomOver (j ≫ ι ≫ N.g) (ι ≫ N.g)))
      (⟨ι, rfl⟩ : SchemeHomOver (ι ≫ N.g) N.g) := by
  unfold gp
  exact N.pts.apply_symm_apply _

theorem pts_gp_val (φ : WithConv (H →ₐ[ℤ] Qb)) : (N.pts (gp N ι j ePts φ)).1 = (ePts Qb φ).1 ≫ j ≫ ι := by
  rw [pts_gp]
  simp only [NeronModelInfra.schemeHomOverComp_coe, Category.assoc]

theorem gp_injective [Mono j]
    (hK_inj : ∀ {T : Scheme.{0}} (t : T ⟶ ℤS),
      Function.Injective (fun y : SchemeHomOver t (ι ≫ N.g) => NMIcomp y (⟨ι, rfl⟩ : SchemeHomOver (ι ≫ N.g) N.g))) :
    Function.Injective (gp N ι j ePts) := by
  intro φ ψ h
  have h1 := congrArg N.pts h
  rw [pts_gp, pts_gp] at h1
  have h2 := hK_inj _ h1
  have h3 : (ePts Qb φ).1 ≫ j = (ePts Qb ψ).1 ≫ j := congrArg Subtype.val h2
  exact (ePts Qb).injective (Subtype.ext ((cancel_mono j).mp h3))

end FltWs11.RoadB.SecA

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve

noncomputable section

namespace FltWs11
namespace RoadB
namespace SecB

universe u

local notation "ℤS" => Spec (CommRingCat.of ℤ)
local notation "Qb" => AlgebraicClosure ℚ

abbrev Aemb (A : ValuationSubring Qb) : ↥A →ₐ[ℤ] Qb := (A.subtype).toIntAlgHom

abbrev toGeneric {H : Type} [CommRing H] [Algebra ℤ H] (A : ValuationSubring Qb)
    (φ : WithConv (H →ₐ[ℤ] ↥A)) : WithConv (H →ₐ[ℤ] Qb) :=
  WithConv.toConv ((Aemb A).comp (WithConv.ofConv φ))

theorem toGeneric_apply {H : Type} [CommRing H] [Algebra ℤ H] (A : ValuationSubring Qb)
    (φ : WithConv (H →ₐ[ℤ] ↥A)) (h : H) :
    WithConv.ofConv (toGeneric A φ) h = A.subtype (WithConv.ofConv φ h) := rfl

theorem toGeneric_injective {H : Type} [CommRing H] [Algebra ℤ H] (A : ValuationSubring Qb) :
    Function.Injective (toGeneric (H := H) A) := by
  intro φ ψ h
  have h' : (Aemb A).comp (WithConv.ofConv φ) = (Aemb A).comp (WithConv.ofConv ψ) := congrArg WithConv.ofConv h
  apply WithConv.ext
  ext x
  have := AlgHom.congr_fun h' x
  exact congrArg Subtype.val (A.subtype_injective this)

theorem toGeneric_mul {H : Type} [CommRing H] [Bialgebra ℤ H] (A : ValuationSubring Qb)
    (f g : WithConv (H →ₐ[ℤ] ↥A)) : toGeneric A (f * g) = toGeneric A f * toGeneric A g := by
  apply WithConv.ofConv_injective
  change (Aemb A).comp (WithConv.ofConv (f * g)) = _
  rw [AlgHom.comp_convMul_distrib]

variable (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (A : ValuationSubring Qb) (hA : A.LiesOverPrime p) (m : ℕ)
  {H : Type} [CommRing H] [HopfAlgebra ℤ H]

def pFibreMap (gp : WithConv (H →ₐ[ℤ] Qb) → JZero p) (φ : WithConv (H →ₐ[ℤ] ↥A)) : JZero p :=
  gp (toGeneric A φ)

theorem pFibreMap_eq_of_forall (gp : WithConv (H →ₐ[ℤ] Qb) → JZero p)
    (φ : WithConv (H →ₐ[ℤ] ↥A)) (ψ : WithConv (H →ₐ[ℤ] Qb)) (hψ : ∀ h : H, ψ h = A.subtype (φ h)) :
    pFibreMap p A gp φ = gp ψ := by
  unfold pFibreMap
  congr 1
  apply congrArg WithConv.toConv
  ext h
  exact (hψ h).symm

theorem pFibreMap_mul (gp : WithConv (H →ₐ[ℤ] Qb) → JZero p)
    (hconvQ : ∀ f g : WithConv (H →ₐ[ℤ] Qb), gp (f * g) = gp f + gp g)
    (hgen : ∀ f g : WithConv (H →ₐ[ℤ] ↥A), toGeneric A (f * g) = toGeneric A f * toGeneric A g)
    (f g : WithConv (H →ₐ[ℤ] ↥A)) :
    pFibreMap p A gp (f * g) = pFibreMap p A gp f + pFibreMap p A gp g := by
  unfold pFibreMap
  rw [hgen, hconvQ]

end FltWs11.RoadB.SecB

end

namespace FltWs11
namespace RoadB
namespace SecB

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve

local notation "ℤS" => Spec (CommRingCat.of ℤ)
local notation "Qb" => AlgebraicClosure ℚ

def pushAlong {X Y T : Scheme.{0}} {gX : X ⟶ ℤS} {gY : Y ⟶ ℤS} (k : X ⟶ Y) (hk : k ≫ gY = gX)
    {t : T ⟶ ℤS} (s : SchemeHomOver t gX) : SchemeHomOver t gY :=
  ⟨s.1 ≫ k, by rw [Category.assoc, hk, s.2]⟩

@[scoped simp] theorem pushAlong_val {X Y T : Scheme.{0}} {gX : X ⟶ ℤS} {gY : Y ⟶ ℤS} (k : X ⟶ Y)
    (hk : k ≫ gY = gX) {t : T ⟶ ℤS} (s : SchemeHomOver t gX) : (pushAlong k hk s).1 = s.1 ≫ k := rfl

theorem Aemb_toRingHom (A : ValuationSubring Qb) : (Aemb A).toRingHom = A.subtype := rfl

theorem pFibreMap_mem_jZeroToricTorsion
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hqp : q ≠ p)
    (A : ValuationSubring Qb) (hA : A.LiesOverPrime p) (N : JZeroNeronIdentityComponent p) (m : ℕ)
    {E : Scheme.{0}} (gE : E ⟶ ℤS) (k : E ⟶ N.G) (hk : k ≫ N.g = gE)
    {H : Type} [CommRing H] [HopfAlgebra ℤ H]
    (ePts : ∀ (T : Type) [CommRing T] [Algebra ℤ T],
      WithConv (H →ₐ[ℤ] T) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ T))) gE)
    (hnat : ∀ (T T' : Type) [CommRing T] [Algebra ℤ T] [CommRing T'] [Algebra ℤ T']
        (σ : T →ₐ[ℤ] T') (φ : WithConv (H →ₐ[ℤ] T)),
      (ePts T' (.toConv (σ.comp φ.ofConv))).1 = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (ePts T φ).1)
    (gp : WithConv (H →ₐ[ℤ] Qb) → JZero p)
    (hgp : ∀ ψ, (N.pts (gp ψ)).1 = (ePts Qb ψ).1 ≫ k)
    (hgp_tors : ∀ ψ, gp ψ ∈ jZeroTorsion p (q ^ m))
    (φ : WithConv (H →ₐ[ℤ] ↥A)) :
    pFibreMap p A gp φ ∈ jZeroToricTorsion p A (q ^ m) := by
  have hndvd : ¬ p ∣ q ^ m := by
    intro h
    have hp : p.Prime := Fact.out
    have hq : q.Prime := Fact.out
    exact hqp ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h)).symm
  have hset := N.torsion_over_p A hA (q ^ m) hndvd
  have hx : pFibreMap p A gp φ ∈ {x : JZero p | x ∈ jZeroTorsion p (q ^ m) ∧
      ∃ s : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) N.g,
        (N.pts x).1 = Spec.map (CommRingCat.ofHom A.subtype) ≫ s.1} := by
    refine ⟨hgp_tors _, pushAlong k hk (ePts (↥A) φ), ?_⟩
    unfold pFibreMap
    rw [hgp, pushAlong_val, ← Category.assoc]
    congr 1
    exact hnat (↥A) Qb (Aemb A) φ
  rw [hset] at hx
  exact hx

end FltWs11.RoadB.SecB
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11"

namespace FltWs11
namespace RoadB
namespace SecB

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

local notation "ℤS" => Spec (CommRingCat.of ℤ)
local notation "Qb" => AlgebraicClosure ℚ
local notation "NMIcomp" => NeronModelInfra.schemeHomOverComp
local notation "GRJcomp" => GoodReductionJacobian.schemeHomOverComp

theorem spec_subtype_comp (A : ValuationSubring Qb) :
    Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))
      = Spec.map (CommRingCat.ofHom (algebraMap ℤ Qb)) := by
  have h : A.subtype.comp (algebraMap ℤ ↥A) = algebraMap ℤ Qb := RingHom.ext_int _ _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

section PtsLemmas

variable {p : ℕ} [Fact p.Prime] (N : JZeroNeronIdentityComponent p)

theorem pts_zero : N.pts 0 = N.L.one _ := by
  have h := N.pts_add 0 0
  rw [add_zero] at h

  have h1 := N.L.inv_mul_cancel _ (N.pts 0)
  calc N.pts 0 = N.L.mul _ (N.L.one _) (N.pts 0) := (N.L.one_mul _ _).symm
    _ = N.L.mul _ (N.L.mul _ (N.L.inv _ (N.pts 0)) (N.pts 0)) (N.pts 0) := by rw [h1]
    _ = N.L.mul _ (N.L.inv _ (N.pts 0)) (N.L.mul _ (N.pts 0) (N.pts 0)) := N.L.mul_assoc _ _ _ _
    _ = N.L.mul _ (N.L.inv _ (N.pts 0)) (N.pts 0) := by rw [← h]
    _ = N.L.one _ := h1

theorem pts_nsmul (n : ℕ) (x : JZero p) : N.pts (n • x) = N.L.nsmul _ n (N.pts x) := by
  induction n with
  | zero => rw [zero_nsmul, pts_zero, GoodReductionJacobian.RelativeGroupLaw.nsmul_zero]
  | succ n ih => rw [succ_nsmul, N.pts_add, ih, GoodReductionJacobian.RelativeGroupLaw.nsmul_succ]

end PtsLemmas
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB"

theorem pFibreMap_surjOn
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hqp : q ≠ p)
    (A : ValuationSubring Qb) (hA : A.LiesOverPrime p) (N : JZeroNeronIdentityComponent p) (m : ℕ)

    {Am : Scheme.{0}} (ι : Am ⟶ N.G) [IsSeparated (ι ≫ N.g)]
    (hK_inj : ∀ {T : Scheme.{0}} (t : T ⟶ ℤS),
      Function.Injective (fun y : SchemeHomOver t (ι ≫ N.g) => NMIcomp y (⟨ι, rfl⟩ : SchemeHomOver (ι ≫ N.g) N.g)))
    (hK_pts : ∀ {T : Scheme.{0}} (t : T ⟶ ℤS) (x : SchemeHomOver t N.g),
      x ∈ N.L.torsionSubset t (q ^ m) ↔ ∃ y : SchemeHomOver t (ι ≫ N.g), NMIcomp y ⟨ι, rfl⟩ = x)

    (e : SchemeHomOver (ι ≫ N.g) (ι ≫ N.g))
    {E : Scheme.{0}} (j : E ⟶ Am)
    (hE_pts : ∀ {T : Scheme.{0}} (t : T ⟶ ℤS) (x : SchemeHomOver t (ι ≫ N.g)),
      NMIcomp x e = x ↔ ∃ y : SchemeHomOver t (j ≫ ι ≫ N.g), NMIcomp y ⟨j, rfl⟩ = x)

    (t : letI := heckeModuleBar p; HeckeAlg)
    (ht : letI := heckeModuleBar p
      ∀ x : JZero p, x ∈ jZeroTorsion p (q ^ m) → (t • x = x ↔ x ∈ eisensteinPrimaryTorsionBar p q m))
    (he_gen : letI := heckeModuleBar p
      ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ Qb))) (ι ≫ N.g),
        N.pts.symm (NMIcomp (NMIcomp x e) ⟨ι, rfl⟩) = t • N.pts.symm (NMIcomp x ⟨ι, rfl⟩))

    {H : Type} [CommRing H] [HopfAlgebra ℤ H]
    (ePts : ∀ (T : Type) [CommRing T] [Algebra ℤ T],
      WithConv (H →ₐ[ℤ] T) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ T))) (j ≫ ι ≫ N.g))
    (hnat : ∀ (T T' : Type) [CommRing T] [Algebra ℤ T] [CommRing T'] [Algebra ℤ T']
        (σ : T →ₐ[ℤ] T') (φ : WithConv (H →ₐ[ℤ] T)),
      (ePts T' (.toConv (σ.comp φ.ofConv))).1 = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (ePts T φ).1)

    (gp : WithConv (H →ₐ[ℤ] Qb) → JZero p)
    (hgp : ∀ ψ, (N.pts (gp ψ)).1 = (ePts Qb ψ).1 ≫ j ≫ ι)
    (y : JZero p) (hy : y ∈ toricEisensteinPrimaryPart p q A hA m) :
    ∃ φ : WithConv (H →ₐ[ℤ] ↥A), pFibreMap p A gp φ = y := by
  letI := heckeModuleBar p
  haveI : IsSeparated N.g := N.separated
  obtain ⟨hyT, hyV⟩ := hy

  have hndvd : ¬ p ∣ q ^ m := by
    intro h
    have hp : p.Prime := Fact.out
    have hq : q.Prime := Fact.out
    exact hqp ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h)).symm
  have hset := N.torsion_over_p A hA (q ^ m) hndvd
  let tA : Spec (CommRingCat.of ↥A) ⟶ ℤS := Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))
  let tQ : Spec (CommRingCat.of Qb) ⟶ ℤS := Spec.map (CommRingCat.ofHom (algebraMap ℤ Qb))
  have hy' : y ∈ {x : JZero p | x ∈ jZeroTorsion p (q ^ m) ∧
      ∃ s : SchemeHomOver tA N.g, (N.pts x).1 = Spec.map (CommRingCat.ofHom A.subtype) ≫ s.1} := by
    rw [hset]; exact hyT
  obtain ⟨hy_tors, s, hs⟩ := hy'
  have hgen : Spec.map (CommRingCat.ofHom A.subtype) ≫ tA = tQ := spec_subtype_comp A

  have hs_gen : GRJcomp (Spec.map (CommRingCat.ofHom A.subtype)) hgen s = N.pts y :=
    Subtype.ext hs.symm

  have hy_tors' : (q ^ m) • y = 0 := by
    have : ((q ^ m : ℕ) : ℤ) • y = 0 := (Submodule.mem_torsionBy_iff _ _).mp hy_tors
    rwa [natCast_zsmul] at this
  have hstors : s ∈ N.L.torsionSubset tA (q ^ m) := by
    change N.L.nsmul tA (q ^ m) s = N.L.one tA
    apply Subtype.ext
    apply AlgebraicGeometry.IsSeparated.eq_of_spec_map_subtype_comp_eq N.g A
    · change (GRJcomp (Spec.map (CommRingCat.ofHom A.subtype)) hgen (N.L.nsmul tA (q ^ m) s)).1
          = (GRJcomp (Spec.map (CommRingCat.ofHom A.subtype)) hgen (N.L.one tA)).1
      rw [GoodReductionJacobian.RelativeGroupLaw.nsmul_natural, hs_gen, ← pts_nsmul, hy_tors', pts_zero,
        GoodReductionJacobian.RelativeGroupLaw.one_natural]
    · rw [(N.L.nsmul tA (q ^ m) s).2, (N.L.one tA).2]

  obtain ⟨s₁, hs₁⟩ := (hK_pts tA s).mp hstors

  let x₁ : SchemeHomOver tQ (ι ≫ N.g) := GRJcomp (Spec.map (CommRingCat.ofHom A.subtype)) hgen s₁
  have hx₁G : NMIcomp x₁ ⟨ι, rfl⟩ = N.pts y := by
    apply Subtype.ext
    change (Spec.map (CommRingCat.ofHom A.subtype) ≫ s₁.1) ≫ ι = (N.pts y).1
    rw [Category.assoc, show s₁.1 ≫ ι = s.1 from congrArg Subtype.val hs₁, ← hs]
  have hty : t • y = y := (ht y hy_tors).mpr hyV
  have hx₁fix : NMIcomp x₁ e = x₁ := by
    apply hK_inj tQ
    apply N.pts.symm.injective
    change N.pts.symm (NMIcomp (NMIcomp x₁ e) ⟨ι, rfl⟩) = N.pts.symm (NMIcomp x₁ ⟨ι, rfl⟩)
    rw [he_gen x₁, hx₁G, Equiv.symm_apply_apply, hty]
  have hfixed : NMIcomp s₁ e = s₁ := by
    apply Subtype.ext
    apply AlgebraicGeometry.IsSeparated.eq_of_spec_map_subtype_comp_eq (ι ≫ N.g) A
    · have := congrArg Subtype.val hx₁fix
      simpa only [x₁, NeronModelInfra.schemeHomOverComp_coe, GoodReductionJacobian.schemeHomOverComp_coe,
        Category.assoc] using this
    · rw [(NMIcomp s₁ e).2, s₁.2]

  obtain ⟨s₂, hs₂⟩ := (hE_pts tA s₁).mp hfixed

  refine ⟨(ePts ↥A).symm s₂, ?_⟩
  apply N.pts.injective
  apply Subtype.ext
  unfold pFibreMap
  rw [hgp, hnat (↥A) Qb (Aemb A), Equiv.apply_symm_apply, Aemb_toRingHom, Category.assoc, hs]
  congr 1
  rw [← Category.assoc, show s₂.1 ≫ j = s₁.1 from congrArg Subtype.val hs₂,
    show s₁.1 ≫ ι = s.1 from congrArg Subtype.val hs₁]

end FltWs11.RoadB.SecB
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB"

namespace FltWs11
namespace RoadB
namespace SecB

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

local notation "Qb" => AlgebraicClosure ℚ

noncomputable def pFibreEquiv (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (A : ValuationSubring Qb) (hA : A.LiesOverPrime p)
    (m : ℕ) {H : Type} [CommRing H] [HopfAlgebra ℤ H]
    (gp : WithConv (H →ₐ[ℤ] Qb) → JZero p) (hgp_inj : Function.Injective gp)
    (hgp_memV : ∀ ψ, gp ψ ∈ eisensteinPrimaryTorsionBar p q m)
    (hmemT : ∀ φ : WithConv (H →ₐ[ℤ] ↥A), pFibreMap p A gp φ ∈ jZeroToricTorsion p A (q ^ m))
    (hsurj : ∀ y ∈ toricEisensteinPrimaryPart p q A hA m, ∃ φ : WithConv (H →ₐ[ℤ] ↥A), pFibreMap p A gp φ = y) :
    WithConv (H →ₐ[ℤ] ↥A) ≃ ↥(toricEisensteinPrimaryPart p q A hA m) :=
  Equiv.ofBijective (fun φ => ⟨pFibreMap p A gp φ, ⟨hmemT φ, hgp_memV _⟩⟩)
    ⟨fun φ ψ h => toGeneric_injective A (hgp_inj (congrArg Subtype.val h)),
     fun y => by
      obtain ⟨φ, hφ⟩ := hsurj y.1 y.2
      exact ⟨φ, Subtype.ext hφ⟩⟩

@[scoped simp] theorem pFibreEquiv_apply_val (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (A : ValuationSubring Qb)
    (hA : A.LiesOverPrime p) (m : ℕ) {H : Type} [CommRing H] [HopfAlgebra ℤ H]
    (gp : WithConv (H →ₐ[ℤ] Qb) → JZero p) (hgp_inj : Function.Injective gp)
    (hgp_memV : ∀ ψ, gp ψ ∈ eisensteinPrimaryTorsionBar p q m)
    (hmemT : ∀ φ : WithConv (H →ₐ[ℤ] ↥A), pFibreMap p A gp φ ∈ jZeroToricTorsion p A (q ^ m))
    (hsurj : ∀ y ∈ toricEisensteinPrimaryPart p q A hA m, ∃ φ : WithConv (H →ₐ[ℤ] ↥A), pFibreMap p A gp φ = y)
    (φ : WithConv (H →ₐ[ℤ] ↥A)) :
    ((pFibreEquiv p q A hA m gp hgp_inj hgp_memV hmemT hsurj φ : ↥(toricEisensteinPrimaryPart p q A hA m)) : JZero p)
      = pFibreMap p A gp φ := rfl

theorem pFibreEquiv_mul (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (A : ValuationSubring Qb)
    (hA : A.LiesOverPrime p) (m : ℕ) {H : Type} [CommRing H] [HopfAlgebra ℤ H]
    (gp : WithConv (H →ₐ[ℤ] Qb) → JZero p) (hgp_inj : Function.Injective gp)
    (hgp_memV : ∀ ψ, gp ψ ∈ eisensteinPrimaryTorsionBar p q m)
    (hmemT : ∀ φ : WithConv (H →ₐ[ℤ] ↥A), pFibreMap p A gp φ ∈ jZeroToricTorsion p A (q ^ m))
    (hsurj : ∀ y ∈ toricEisensteinPrimaryPart p q A hA m, ∃ φ : WithConv (H →ₐ[ℤ] ↥A), pFibreMap p A gp φ = y)
    (hconvQ : ∀ f g : WithConv (H →ₐ[ℤ] Qb), gp (f * g) = gp f + gp g)
    (f g : WithConv (H →ₐ[ℤ] ↥A)) :
    pFibreEquiv p q A hA m gp hgp_inj hgp_memV hmemT hsurj (f * g)
      = pFibreEquiv p q A hA m gp hgp_inj hgp_memV hmemT hsurj f
        + pFibreEquiv p q A hA m gp hgp_inj hgp_memV hmemT hsurj g := by
  apply Subtype.ext
  change pFibreMap p A gp (f * g) = pFibreMap p A gp f + pFibreMap p A gp g
  exact pFibreMap_mul p A gp hconvQ (toGeneric_mul A) f g

end FltWs11.RoadB.SecB
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB"

namespace FltWs11
namespace RoadB
namespace SecA

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra ModularCurve

local notation "ℤS" => Spec (CommRingCat.of ℤ)
local notation "Qb" => AlgebraicClosure ℚ
local notation "NMIcomp" => NeronModelInfra.schemeHomOverComp
local notation "tQ" => Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))

section

variable {p : ℕ} [Fact p.Prime] (q : ℕ) [Fact q.Prime] (N : JZeroNeronIdentityComponent p) (m : ℕ)
  {Am : Scheme.{0}} (ι : Am ⟶ N.G) {E : Scheme.{0}} (j : E ⟶ Am)
  {H : Type} [CommRing H] [HopfAlgebra ℤ H]
  (ePts : ∀ (T : Type) [CommRing T] [Algebra ℤ T],
    WithConv (H →ₐ[ℤ] T) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ T))) (j ≫ ι ≫ N.g))

  (hK_pts : ∀ {T : Scheme.{0}} (t : T ⟶ ℤS) (x : SchemeHomOver t N.g),
    x ∈ N.L.torsionSubset t (q ^ m) ↔ ∃ y : SchemeHomOver t (ι ≫ N.g), NMIcomp y (⟨ι, rfl⟩ : SchemeHomOver (ι ≫ N.g) N.g) = x)
  (hK_inj : ∀ {T : Scheme.{0}} (t : T ⟶ ℤS),
    Function.Injective (fun y : SchemeHomOver t (ι ≫ N.g) => NMIcomp y (⟨ι, rfl⟩ : SchemeHomOver (ι ≫ N.g) N.g)))

  (e : SchemeHomOver (ι ≫ N.g) (ι ≫ N.g))
  (hE_pts : ∀ {T : Scheme.{0}} (t : T ⟶ ℤS) (x : SchemeHomOver t (ι ≫ N.g)),
    NMIcomp x e = x ↔ ∃ y : SchemeHomOver t (j ≫ ι ≫ N.g), NMIcomp y (⟨j, rfl⟩ : SchemeHomOver (j ≫ ι ≫ N.g) (ι ≫ N.g)) = x)

  (t : letI := heckeModuleBar p; HeckeAlg)
  (ht : letI := heckeModuleBar p
    ∀ x : JZero p, (q ^ m : ℤ) • x = 0 → (t • x = x ↔ x ∈ eisensteinPrimaryTorsionBar p q m))
  (φt : SchemeHomOver N.g N.g)
  (hφt : letI := heckeModuleBar p; ∀ x : JZero p, (N.pts (t • x)).1 = (N.pts x).1 ≫ φt.1)
  (heφ : e.1 ≫ ι = ι ≫ φt.1)

include hK_pts in

theorem zsmul_eq_zero_of_pts_eq (x : JZero p) (y : SchemeHomOver tQ (ι ≫ N.g))
    (hy : NMIcomp y (⟨ι, rfl⟩ : SchemeHomOver (ι ≫ N.g) N.g) = N.pts x) : (q ^ m : ℤ) • x = 0 := by
  have htors : N.pts x ∈ N.L.torsionSubset tQ (q ^ m) := (hK_pts _ _).mpr ⟨y, hy⟩
  change N.L.nsmul tQ (q ^ m) (N.pts x) = N.L.one tQ at htors
  rw [← SecB.pts_nsmul, ← SecB.pts_zero N] at htors
  have := N.pts.injective htors
  have h2 : ((q ^ m : ℕ) : ℤ) • x = 0 := by rw [natCast_zsmul]; exact this
  exact_mod_cast h2

include hK_pts hE_pts hφt heφ in

theorem smul_eq_of_pts_eq (x : JZero p) (z : SchemeHomOver tQ (j ≫ ι ≫ N.g))
    (hz : NMIcomp (NMIcomp z (⟨j, rfl⟩ : SchemeHomOver (j ≫ ι ≫ N.g) (ι ≫ N.g))) (⟨ι, rfl⟩ : SchemeHomOver (ι ≫ N.g) N.g)
      = N.pts x) :
    (letI := heckeModuleBar p; t • x) = x := by
  letI := heckeModuleBar p
  apply N.pts.injective
  apply Subtype.ext
  have hfix : NMIcomp (NMIcomp z (⟨j, rfl⟩ : SchemeHomOver (j ≫ ι ≫ N.g) (ι ≫ N.g))) e
      = NMIcomp z ⟨j, rfl⟩ := (hE_pts _ _).mpr ⟨z, rfl⟩
  have hfix' : (z.1 ≫ j) ≫ e.1 = z.1 ≫ j := congrArg Subtype.val hfix
  rw [hφt x, ← congrArg Subtype.val hz]
  change ((z.1 ≫ j) ≫ ι) ≫ φt.1 = (z.1 ≫ j) ≫ ι
  rw [Category.assoc, ← heφ, ← Category.assoc, hfix']

include hK_pts hE_pts ht hφt heφ in

theorem gp_mem (φ : WithConv (H →ₐ[ℤ] Qb)) : gp N ι j ePts φ ∈ eisensteinPrimaryTorsionBar p q m := by
  letI := heckeModuleBar p
  have hpts := pts_gp N ι j ePts φ
  have h0 := zsmul_eq_zero_of_pts_eq q N m ι hK_pts (gp N ι j ePts φ) (NMIcomp (ePts Qb φ) ⟨j, rfl⟩) hpts.symm
  exact (ht _ h0).mp (smul_eq_of_pts_eq q N m ι j hK_pts e hE_pts t φt hφt heφ _ (ePts Qb φ) hpts.symm)

include hK_pts hK_inj hE_pts ht hφt heφ in

theorem gp_surjOn (y : JZero p) (hy : y ∈ eisensteinPrimaryTorsionBar p q m) : ∃ φ, gp N ι j ePts φ = y := by
  letI := heckeModuleBar p

  have hyq : (q ^ m : ℤ) • y = 0 := by
    have := hy.1
    change ((q ^ m : ℤ) • AddMonoidHom.id (JZero p)) y = 0 at this
    simpa using this
  have hty : t • y = y := (ht y hyq).mpr hy

  have htors : N.pts y ∈ N.L.torsionSubset tQ (q ^ m) := by
    change N.L.nsmul tQ (q ^ m) (N.pts y) = N.L.one tQ
    rw [← SecB.pts_nsmul, ← SecB.pts_zero N]
    have : ((q ^ m : ℕ) : ℤ) • y = 0 := by exact_mod_cast hyq
    rw [natCast_zsmul] at this
    rw [this]
  obtain ⟨x₁, hx₁⟩ := (hK_pts _ _).mp htors

  have hfix : NMIcomp x₁ e = x₁ := by
    apply hK_inj
    apply Subtype.ext
    change (x₁.1 ≫ e.1) ≫ ι = x₁.1 ≫ ι
    rw [Category.assoc, heφ, ← Category.assoc, show x₁.1 ≫ ι = (N.pts y).1 from congrArg Subtype.val hx₁, ← hφt, hty]
  obtain ⟨x₂, hx₂⟩ := (hE_pts _ _).mp hfix
  refine ⟨(ePts Qb).symm x₂, ?_⟩
  apply N.pts.injective
  rw [pts_gp, Equiv.apply_symm_apply, hx₂, hx₁]

end
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB"

end FltWs11.RoadB.SecA
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB"

namespace FltWs11
namespace RoadB
namespace SecA

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra ModularCurve

local notation "ℤS" => Spec (CommRingCat.of ℤ)
local notation "Qb" => AlgebraicClosure ℚ
local notation "NMIcomp" => NeronModelInfra.schemeHomOverComp
local notation "tQ" => Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))

section

variable {p : ℕ} [Fact p.Prime] (N : JZeroNeronIdentityComponent p)
  {Am : Scheme.{0}} (ι : Am ⟶ N.G) {E : Scheme.{0}} (j : E ⟶ Am)
  {H : Type} [CommRing H] [HopfAlgebra ℤ H]
  (ePts : ∀ (T : Type) [CommRing T] [Algebra ℤ T],
    WithConv (H →ₐ[ℤ] T) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ T))) (j ≫ ι ≫ N.g))
  (LK : GoodReductionJacobian.RelativeGroupLaw ℤ (ι ≫ N.g)) (LE : GoodReductionJacobian.RelativeGroupLaw ℤ (j ≫ ι ≫ N.g))
  (hconv : ∀ (T : Type) [CommRing T] [Algebra ℤ T] (φ ψ : WithConv (H →ₐ[ℤ] T)),
    ePts T (φ * ψ) = LE.mul _ (ePts T φ) (ePts T ψ))
  (hj_hom : ∀ {T : Scheme.{0}} (s : T ⟶ ℤS) (x y : SchemeHomOver s (j ≫ ι ≫ N.g)),
    NMIcomp (LE.mul s x y) (⟨j, rfl⟩ : SchemeHomOver (j ≫ ι ≫ N.g) (ι ≫ N.g))
      = LK.mul s (NMIcomp x ⟨j, rfl⟩) (NMIcomp y ⟨j, rfl⟩))
  (hLKhom : ∀ {T : Scheme.{0}} (s : T ⟶ ℤS) (x y : SchemeHomOver s (ι ≫ N.g)),
    NMIcomp (LK.mul s x y) (⟨ι, rfl⟩ : SchemeHomOver (ι ≫ N.g) N.g) = N.L.mul s (NMIcomp x ⟨ι, rfl⟩) (NMIcomp y ⟨ι, rfl⟩))
  (hnat : ∀ (T T' : Type) [CommRing T] [Algebra ℤ T] [CommRing T'] [Algebra ℤ T']
      (σ : T →ₐ[ℤ] T') (φ : WithConv (H →ₐ[ℤ] T)),
    (ePts T' (.toConv (σ.comp φ.ofConv))).1 = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (ePts T φ).1)

include hconv hj_hom hLKhom in

theorem gp_mul (φ ψ : WithConv (H →ₐ[ℤ] Qb)) :
    gp N ι j ePts (φ * ψ) = gp N ι j ePts φ + gp N ι j ePts ψ := by
  apply N.pts.injective
  rw [N.pts_add, pts_gp, pts_gp, pts_gp, hconv, hj_hom, hLKhom]

include hnat in

theorem gp_galois (σ : Qb ≃ₐ[ℚ] Qb) (f g : WithConv (H →ₐ[ℤ] Qb)) (hfg : ∀ h : H, g h = σ (f h)) :
    gp N ι j ePts g = σ • gp N ι j ePts f := by
  let σ' : Qb →ₐ[ℤ] Qb := (σ : Qb →+* Qb).toIntAlgHom
  have hg : g = WithConv.toConv (σ'.comp (WithConv.ofConv f)) := by
    apply WithConv.ext
    ext h
    exact hfg h
  apply N.pts.injective
  apply Subtype.ext
  rw [N.pts_galois, pts_gp_val, pts_gp_val, hg, hnat Qb Qb σ' f, Category.assoc]
  rfl

end
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB"

noncomputable def genericEquiv {p : ℕ} [Fact p.Prime] (q : ℕ) [Fact q.Prime] (N : JZeroNeronIdentityComponent p) (m : ℕ)
    {Am : Scheme.{0}} (ι : Am ⟶ N.G) {E : Scheme.{0}} (j : E ⟶ Am)
    {H : Type} [CommRing H] [HopfAlgebra ℤ H]
    (ePts : ∀ (T : Type) [CommRing T] [Algebra ℤ T],
      WithConv (H →ₐ[ℤ] T) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ T))) (j ≫ ι ≫ N.g))
    (hinj : Function.Injective (gp N ι j ePts))
    (hmem : ∀ φ, gp N ι j ePts φ ∈ eisensteinPrimaryTorsionBar p q m)
    (hsurj : ∀ y ∈ eisensteinPrimaryTorsionBar p q m, ∃ φ, gp N ι j ePts φ = y) :
    WithConv (H →ₐ[ℤ] Qb) ≃ ↥(eisensteinPrimaryTorsionBar p q m) :=
  Equiv.ofBijective (fun φ => ⟨gp N ι j ePts φ, hmem φ⟩)
    ⟨fun a b h => hinj (congrArg Subtype.val h), fun y => by
      obtain ⟨φ, hφ⟩ := hsurj y.1 y.2
      exact ⟨φ, Subtype.ext hφ⟩⟩

@[scoped simp] theorem genericEquiv_apply_val {p : ℕ} [Fact p.Prime] (q : ℕ) [Fact q.Prime] (N : JZeroNeronIdentityComponent p) (m : ℕ)
    {Am : Scheme.{0}} (ι : Am ⟶ N.G) {E : Scheme.{0}} (j : E ⟶ Am)
    {H : Type} [CommRing H] [HopfAlgebra ℤ H]
    (ePts : ∀ (T : Type) [CommRing T] [Algebra ℤ T],
      WithConv (H →ₐ[ℤ] T) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ T))) (j ≫ ι ≫ N.g))
    (hinj : Function.Injective (gp N ι j ePts))
    (hmem : ∀ φ, gp N ι j ePts φ ∈ eisensteinPrimaryTorsionBar p q m)
    (hsurj : ∀ y ∈ eisensteinPrimaryTorsionBar p q m, ∃ φ, gp N ι j ePts φ = y) (φ : WithConv (H →ₐ[ℤ] Qb)) :
    ((genericEquiv q N m ι j ePts hinj hmem hsurj φ : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p) = gp N ι j ePts φ :=
  rfl

end FltWs11.RoadB.SecA
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecA"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB"

namespace FltWs11
namespace RoadB
namespace SecA

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra ModularCurve

local notation "Qb" => AlgebraicClosure ℚ
local notation "NMIcomp" => NeronModelInfra.schemeHomOverComp
local notation "tQ" => Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))

theorem he_gen_of {p : ℕ} [Fact p.Prime] (N : JZeroNeronIdentityComponent p)
    {Am : Scheme.{0}} (ι : Am ⟶ N.G) (e : SchemeHomOver (ι ≫ N.g) (ι ≫ N.g))
    (t : letI := heckeModuleBar p; HeckeAlg) (φt : SchemeHomOver N.g N.g)
    (hφt : letI := heckeModuleBar p; ∀ x : JZero p, (N.pts (t • x)).1 = (N.pts x).1 ≫ φt.1)
    (heφ : e.1 ≫ ι = ι ≫ φt.1)
    (x : SchemeHomOver tQ (ι ≫ N.g)) :
    letI := heckeModuleBar p
    N.pts.symm (NMIcomp (NMIcomp x e) (⟨ι, rfl⟩ : SchemeHomOver (ι ≫ N.g) N.g))
      = t • N.pts.symm (NMIcomp x (⟨ι, rfl⟩ : SchemeHomOver (ι ≫ N.g) N.g)) := by
  letI := heckeModuleBar p
  apply N.pts.injective
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  rw [hφt, Equiv.apply_symm_apply]
  change (x.1 ≫ e.1) ≫ ι = (x.1 ≫ ι) ≫ φt.1
  rw [Category.assoc, heφ, Category.assoc]

end FltWs11.RoadB.SecA
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecA"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecA"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecA"

namespace FltWs11
namespace RoadB
namespace SecC

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra ModularCurve

local notation "ℤS" => Spec (CommRingCat.of ℤ)
local notation "NMIcomp" => NeronModelInfra.schemeHomOverComp

theorem hu_of {p : ℕ} [Fact p.Prime] (N : JZeroNeronIdentityComponent p)
    {Am Am' : Scheme.{0}} (ι : Am ⟶ N.G) (ι' : Am' ⟶ N.G)
    {E E' : Scheme.{0}} (j : E ⟶ Am) (j' : E' ⟶ Am') [Mono j']
    (LK : GoodReductionJacobian.RelativeGroupLaw ℤ (ι ≫ N.g)) (LK' : GoodReductionJacobian.RelativeGroupLaw ℤ (ι' ≫ N.g))
    (LE : GoodReductionJacobian.RelativeGroupLaw ℤ (j ≫ ι ≫ N.g)) (LE' : GoodReductionJacobian.RelativeGroupLaw ℤ (j' ≫ ι' ≫ N.g))
    (hj_hom : ∀ {T : Scheme.{0}} (s : T ⟶ ℤS) (x y : SchemeHomOver s (j ≫ ι ≫ N.g)),
      NMIcomp (LE.mul s x y) (⟨j, rfl⟩ : SchemeHomOver (j ≫ ι ≫ N.g) (ι ≫ N.g)) = LK.mul s (NMIcomp x ⟨j, rfl⟩) (NMIcomp y ⟨j, rfl⟩))
    (hLKhom : ∀ {T : Scheme.{0}} (s : T ⟶ ℤS) (x y : SchemeHomOver s (ι ≫ N.g)),
      NMIcomp (LK.mul s x y) (⟨ι, rfl⟩ : SchemeHomOver (ι ≫ N.g) N.g) = N.L.mul s (NMIcomp x ⟨ι, rfl⟩) (NMIcomp y ⟨ι, rfl⟩))
    (hj_hom' : ∀ {T : Scheme.{0}} (s : T ⟶ ℤS) (x y : SchemeHomOver s (j' ≫ ι' ≫ N.g)),
      NMIcomp (LE'.mul s x y) (⟨j', rfl⟩ : SchemeHomOver (j' ≫ ι' ≫ N.g) (ι' ≫ N.g)) = LK'.mul s (NMIcomp x ⟨j', rfl⟩) (NMIcomp y ⟨j', rfl⟩))
    (hLKhom' : ∀ {T : Scheme.{0}} (s : T ⟶ ℤS) (x y : SchemeHomOver s (ι' ≫ N.g)),
      NMIcomp (LK'.mul s x y) (⟨ι', rfl⟩ : SchemeHomOver (ι' ≫ N.g) N.g) = N.L.mul s (NMIcomp x ⟨ι', rfl⟩) (NMIcomp y ⟨ι', rfl⟩))
    (hK_inj' : ∀ {T : Scheme.{0}} (t : T ⟶ ℤS),
      Function.Injective (fun y : SchemeHomOver t (ι' ≫ N.g) => NMIcomp y (⟨ι', rfl⟩ : SchemeHomOver (ι' ≫ N.g) N.g)))
    (u : SchemeHomOver (j ≫ ι ≫ N.g) (j' ≫ ι' ≫ N.g)) (hu1 : u.1 ≫ j' ≫ ι' = j ≫ ι) :
    ∀ {T : Scheme.{0}} (t : T ⟶ ℤS) (x y : SchemeHomOver t (j ≫ ι ≫ N.g)),
      (⟨(LE.mul t x y).1 ≫ u.1, by rw [Category.assoc, u.2, (LE.mul t x y).2]⟩ : SchemeHomOver t (j' ≫ ι' ≫ N.g)) =
        LE'.mul t ⟨x.1 ≫ u.1, by rw [Category.assoc, u.2, x.2]⟩ ⟨y.1 ≫ u.1, by rw [Category.assoc, u.2, y.2]⟩ := by
  intro T t x y

  have hinjE' : Function.Injective (fun z : SchemeHomOver t (j' ≫ ι' ≫ N.g) =>
      NMIcomp (NMIcomp z (⟨j', rfl⟩ : SchemeHomOver (j' ≫ ι' ≫ N.g) (ι' ≫ N.g))) (⟨ι', rfl⟩ : SchemeHomOver (ι' ≫ N.g) N.g)) := by
    intro a b h
    have h2 := hK_inj' t h
    exact Subtype.ext ((cancel_mono j').mp (congrArg Subtype.val h2))
  apply hinjE'
  change NMIcomp (NMIcomp _ ⟨j', rfl⟩) ⟨ι', rfl⟩ = NMIcomp (NMIcomp (LE'.mul t _ _) ⟨j', rfl⟩) ⟨ι', rfl⟩
  rw [hj_hom', hLKhom']

  have key : ∀ z : SchemeHomOver t (j ≫ ι ≫ N.g),
      NMIcomp (NMIcomp (⟨z.1 ≫ u.1, by rw [Category.assoc, u.2, z.2]⟩ : SchemeHomOver t (j' ≫ ι' ≫ N.g)) ⟨j', rfl⟩) ⟨ι', rfl⟩
        = NMIcomp (NMIcomp z (⟨j, rfl⟩ : SchemeHomOver (j ≫ ι ≫ N.g) (ι ≫ N.g))) (⟨ι, rfl⟩ : SchemeHomOver (ι ≫ N.g) N.g) := by
    intro z
    apply Subtype.ext
    change ((z.1 ≫ u.1) ≫ j') ≫ ι' = (z.1 ≫ j) ≫ ι
    simp only [Category.assoc, hu1]
  rw [key x, key y, ← hLKhom, ← hj_hom]
  apply Subtype.ext
  change ((LE.mul t x y).1 ≫ u.1 ≫ j') ≫ ι' = ((LE.mul t x y).1 ≫ j) ≫ ι
  simp only [Category.assoc, hu1]

end FltWs11.RoadB.SecC
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecA"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecA"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecA"

section NsmulPow
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem FltWs11.RoadB.SecC.nsmul_eq_pow {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    letI := G.pointGroup t
    G.nsmul t n x = x ^ n := by
  letI := G.pointGroup t
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [RelativeGroupLaw.nsmul_succ, ih, pow_succ]
    rfl
end NsmulPow
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecA"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra ModularCurve in
theorem FltWs11.RoadB.SecC.exists_levelHom
    {p : ℕ} [Fact p.Prime] (q : ℕ) [Fact q.Prime] (N : JZeroNeronIdentityComponent p) (m : ℕ)

    (hKpts' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℤ)) (x : SchemeHomOver t N.g),
      x ∈ N.L.torsionSubset t (q ^ (m + 1)) ↔
        ∃ y : SchemeHomOver t (FltWs11.RoadB.ιK p q N (m + 1) ≫ N.g),
          NeronModelInfra.schemeHomOverComp y ⟨FltWs11.RoadB.ιK p q N (m + 1), rfl⟩ = x)
    (hKpts : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℤ)) (x : SchemeHomOver t N.g),
      x ∈ N.L.torsionSubset t (q ^ m) ↔
        ∃ y : SchemeHomOver t (FltWs11.RoadB.ιK p q N m ≫ N.g),
          NeronModelInfra.schemeHomOverComp y ⟨FltWs11.RoadB.ιK p q N m, rfl⟩ = x)

    (eK : SchemeHomOver (FltWs11.RoadB.ιK p q N m ≫ N.g) (FltWs11.RoadB.ιK p q N m ≫ N.g))
    (eK' : SchemeHomOver (FltWs11.RoadB.ιK p q N (m + 1) ≫ N.g) (FltWs11.RoadB.ιK p q N (m + 1) ≫ N.g))
    (φt φt' : SchemeHomOver N.g N.g)
    (heφ : eK.1 ≫ FltWs11.RoadB.ιK p q N m = FltWs11.RoadB.ιK p q N m ≫ φt.1)
    (heφ' : eK'.1 ≫ FltWs11.RoadB.ιK p q N (m + 1) = FltWs11.RoadB.ιK p q N (m + 1) ≫ φt'.1)
    (hlevel : FltWs11.RoadB.ιK p q N m ≫ φt'.1 = FltWs11.RoadB.ιK p q N m ≫ φt.1)
    {E E' : Scheme.{0}} (j : E ⟶ N.L.schemeKer (q ^ m)) (j' : E' ⟶ N.L.schemeKer (q ^ (m + 1)))
    [IsClosedImmersion j] [IsClosedImmersion j']
    (hE_pts : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℤ)) (x : SchemeHomOver t (FltWs11.RoadB.ιK p q N m ≫ N.g)),
      NeronModelInfra.schemeHomOverComp x eK = x ↔
        ∃ y : SchemeHomOver t (j ≫ FltWs11.RoadB.ιK p q N m ≫ N.g), NeronModelInfra.schemeHomOverComp y ⟨j, rfl⟩ = x)
    (hE_pts' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℤ)) (x : SchemeHomOver t (FltWs11.RoadB.ιK p q N (m + 1) ≫ N.g)),
      NeronModelInfra.schemeHomOverComp x eK' = x ↔
        ∃ y : SchemeHomOver t (j' ≫ FltWs11.RoadB.ιK p q N (m + 1) ≫ N.g), NeronModelInfra.schemeHomOverComp y ⟨j', rfl⟩ = x) :
    ∃ u : SchemeHomOver (j ≫ FltWs11.RoadB.ιK p q N m ≫ N.g) (j' ≫ FltWs11.RoadB.ιK p q N (m + 1) ≫ N.g),
      u.1 ≫ j' ≫ FltWs11.RoadB.ιK p q N (m + 1) = j ≫ FltWs11.RoadB.ιK p q N m ∧ IsClosedImmersion u.1 := by

  have hιK : ∀ n : ℕ, IsClosedImmersion (pullback.fst (N.L.schemeNsmul n) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1) := by
    intro n
    haveI : IsSeparated N.g := N.separated
    haveI : IsClosedImmersion ((N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g) := by
      rw [(N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).2]
      infer_instance
    haveI : IsClosedImmersion (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 :=
      IsClosedImmersion.of_comp (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 N.g
    exact MorphismProperty.pullback_fst _ _ inferInstance
  have hιK1 : IsClosedImmersion (FltWs11.RoadB.ιK p q N (m + 1)) := hιK (q ^ (m + 1))
  have hιK0 : IsClosedImmersion (FltWs11.RoadB.ιK p q N m) := hιK (q ^ m)

  let x₀ : SchemeHomOver (FltWs11.RoadB.ιK p q N m ≫ N.g) N.g := ⟨FltWs11.RoadB.ιK p q N m, rfl⟩
  have hx₀m : x₀ ∈ N.L.torsionSubset (FltWs11.RoadB.ιK p q N m ≫ N.g) (q ^ m) := by
    refine (hKpts _ x₀).mpr ⟨⟨𝟙 _, Category.id_comp _⟩, Subtype.ext ?_⟩
    change 𝟙 _ ≫ FltWs11.RoadB.ιK p q N m = FltWs11.RoadB.ιK p q N m
    exact Category.id_comp _
  have hx₀m1 : x₀ ∈ N.L.torsionSubset (FltWs11.RoadB.ιK p q N m ≫ N.g) (q ^ (m + 1)) := by
    letI := N.L.pointGroup (FltWs11.RoadB.ιK p q N m ≫ N.g)
    rw [GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset,
      GoodReductionJacobian.RelativeGroupLaw.isTorsionPoint_def, FltWs11.RoadB.SecC.nsmul_eq_pow] at hx₀m ⊢
    rw [pow_succ, pow_mul, hx₀m]
    exact one_pow q
  obtain ⟨y, hy⟩ := (hKpts' _ x₀).mp hx₀m1
  have hy1 : y.1 ≫ FltWs11.RoadB.ιK p q N (m + 1) = FltWs11.RoadB.ιK p q N m := congrArg Subtype.val hy
  have hy1' : ∀ {W : Scheme.{0}} (w : N.G ⟶ W),
      y.1 ≫ FltWs11.RoadB.ιK p q N (m + 1) ≫ w = FltWs11.RoadB.ιK p q N m ≫ w := by
    intro W w
    rw [← Category.assoc, hy1]

  have hjfix : j ≫ eK.1 = j := by
    have h := (hE_pts _ (⟨j, rfl⟩ : SchemeHomOver (j ≫ FltWs11.RoadB.ιK p q N m ≫ N.g)
      (FltWs11.RoadB.ιK p q N m ≫ N.g))).mpr ⟨⟨𝟙 E, Category.id_comp _⟩, Subtype.ext (Category.id_comp _)⟩
    exact congrArg Subtype.val h
  have hjφ : j ≫ FltWs11.RoadB.ιK p q N m ≫ φt.1 = j ≫ FltWs11.RoadB.ιK p q N m := by
    rw [← heφ, ← Category.assoc, hjfix]

  let z : SchemeHomOver (j ≫ FltWs11.RoadB.ιK p q N m ≫ N.g) (FltWs11.RoadB.ιK p q N (m + 1) ≫ N.g) :=
    ⟨j ≫ y.1, by rw [Category.assoc, y.2]⟩
  have hzfix : NeronModelInfra.schemeHomOverComp z eK' = z := by
    apply Subtype.ext
    haveI := hιK1
    rw [← cancel_mono (FltWs11.RoadB.ιK p q N (m + 1))]
    change ((j ≫ y.1) ≫ eK'.1) ≫ FltWs11.RoadB.ιK p q N (m + 1) = (j ≫ y.1) ≫ FltWs11.RoadB.ιK p q N (m + 1)
    rw [Category.assoc, Category.assoc, Category.assoc, heφ', hy1' φt'.1, hy1, hlevel]
    exact hjφ

  obtain ⟨u, hu⟩ := (hE_pts' _ z).mp hzfix
  have hu1 : u.1 ≫ j' = j ≫ y.1 := congrArg Subtype.val hu
  have hcomp : u.1 ≫ j' ≫ FltWs11.RoadB.ιK p q N (m + 1) = j ≫ FltWs11.RoadB.ιK p q N m := by
    rw [← Category.assoc, hu1, Category.assoc, hy1]

  refine ⟨u, hcomp, ?_⟩
  haveI := hιK1
  haveI := hιK0
  haveI : IsClosedImmersion (j' ≫ FltWs11.RoadB.ιK p q N (m + 1)) := inferInstance
  haveI : IsClosedImmersion (u.1 ≫ j' ≫ FltWs11.RoadB.ιK p q N (m + 1)) := by
    rw [hcomp]
    infer_instance
  exact IsClosedImmersion.of_comp u.1 (j' ≫ FltWs11.RoadB.ιK p q N (m + 1))

namespace FltWs11
namespace RoadB
namespace SecD

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme NeronModelInfra

local notation "ℤS" => Spec (CommRingCat.of ℤ)

theorem convMul_comm_of_points
    {E : Scheme.{0}} {gE : E ⟶ ℤS} (LE : GoodReductionJacobian.RelativeGroupLaw ℤ gE)
    (hEcomm : ∀ {T : Scheme.{0}} (t : T ⟶ ℤS) (x y : SchemeHomOver t gE), LE.mul t x y = LE.mul t y x)
    {H : Type} [CommRing H] [HopfAlgebra ℤ H]
    (ePts : ∀ (T : Type) [CommRing T] [Algebra ℤ T],
      WithConv (H →ₐ[ℤ] T) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ T))) gE)
    (hconv : ∀ (T : Type) [CommRing T] [Algebra ℤ T] (φ ψ : WithConv (H →ₐ[ℤ] T)),
      ePts T (φ * ψ) = LE.mul _ (ePts T φ) (ePts T ψ)) :
    ∀ (T : Type) [CommRing T] (f g : WithConv (H →ₐ[ℤ] T)), f * g = g * f := by
  intro T _ f g
  apply (ePts T).injective
  rw [hconv, hconv, hEcomm]

theorem exists_pointsSheaf
    {E : Scheme.{0}} {gE : E ⟶ ℤS} (LE : GoodReductionJacobian.RelativeGroupLaw ℤ gE)
    (hEcomm : ∀ {T : Scheme.{0}} (t : T ⟶ ℤS) (x y : SchemeHomOver t gE), LE.mul t x y = LE.mul t y x)
    (H : Type) [CommRing H] [HopfAlgebra ℤ H]
    (ePts : ∀ (T : Type) [CommRing T] [Algebra ℤ T],
      WithConv (H →ₐ[ℤ] T) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ T))) gE)
    (hconv : ∀ (T : Type) [CommRing T] [Algebra ℤ T] (φ ψ : WithConv (H →ₐ[ℤ] T)),
      ePts T (φ * ψ) = LE.mul _ (ePts T φ) (ePts T ψ)) :
    ∃ (𝒥 : Sheaf (smallFppfTopology specInt) Ab.{1})
      (sE : ∀ U : specInt.Fppf, 𝒥.1.obj (Opposite.op U) ≃+ Additive (WithConv (H →ₐ[ℤ] Γ(U.left, ⊤)))),
      ∀ {U V : specInt.Fppf} (f : U ⟶ V) (s : 𝒥.1.obj (Opposite.op V)) (h : H),
        (Additive.toMul (sE U (𝒥.1.map f.op s))) h
          = (Scheme.Γ.map f.left.op) ((Additive.toMul (sE V s)) h) :=
  HopfAlgebra.exists_sheaf_smallFppfTopology_specInt_sectionsEquiv_algHom H
    (convMul_comm_of_points LE hEcomm ePts hconv)

end FltWs11.RoadB.SecD
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecA"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecA"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecA"

namespace FltWs11
namespace RoadB
namespace SecD

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

theorem exists_cokernel_shortExact
    (𝒥 : ℕ → Sheaf (smallFppfTopology specInt) Ab.{1})
    (incl : ∀ m, 𝒥 m ⟶ 𝒥 (m + 1)) (hmono : ∀ m, Mono (incl m)) :
    ∃ (Q : ℕ → Sheaf (smallFppfTopology specInt) Ab.{1}) (proj : ∀ m, 𝒥 (m + 1) ⟶ Q m)
      (incl_proj : ∀ m, incl m ≫ proj m = 0),
      ∀ m, (ShortComplex.mk (incl m) (proj m) (incl_proj m)).ShortExact := by
  refine ⟨fun m => cokernel (incl m), fun m => cokernel.π (incl m), fun m => cokernel.condition (incl m), fun m => ?_⟩
  haveI := hmono m
  exact ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact (incl m)) (hmono m) inferInstance

end FltWs11.RoadB.SecD
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecA"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecA"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecA"

namespace FltWs11
namespace RoadB
namespace SecD

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

noncomputable def precompMon {H H' : Type} [CommRing H] [HopfAlgebra ℤ H] [CommRing H'] [HopfAlgebra ℤ H']
    (lv : H' →ₐc[ℤ] H) (T : Type) [CommRing T] :
    WithConv (H →ₐ[ℤ] T) →* WithConv (H' →ₐ[ℤ] T) where
  toFun x := WithConv.toConv ((WithConv.ofConv x).comp (lv : H' →ₐ[ℤ] H))
  map_one' := by
    apply WithConv.ofConv_injective
    change (WithConv.ofConv (1 : WithConv (H →ₐ[ℤ] T))).comp (lv : H' →ₐ[ℤ] H)
      = WithConv.ofConv (1 : WithConv (H' →ₐ[ℤ] T))
    rw [AlgHom.convOne_def, AlgHom.convOne_def]
    change ((Algebra.ofId ℤ T).comp (Bialgebra.counitAlgHom ℤ H)).comp (lv : H' →ₐ[ℤ] H) = _
    rw [AlgHom.comp_assoc, BialgHom.counitAlgHom_comp]
  map_mul' x y := by
    apply WithConv.ofConv_injective
    change (WithConv.ofConv (x * y)).comp (lv : H' →ₐ[ℤ] H) = _
    rw [AlgHom.convMul_comp_bialgHom_distrib]

noncomputable def precompAdd {H H' : Type} [CommRing H] [HopfAlgebra ℤ H] [CommRing H'] [HopfAlgebra ℤ H']
    (lv : H' →ₐc[ℤ] H) (T : Type) [CommRing T] :
    Additive (WithConv (H →ₐ[ℤ] T)) →+ Additive (WithConv (H' →ₐ[ℤ] T)) :=
  MonoidHom.toAdditive (precompMon lv T)

theorem precompAdd_apply {H H' : Type} [CommRing H] [HopfAlgebra ℤ H] [CommRing H'] [HopfAlgebra ℤ H']
    (lv : H' →ₐc[ℤ] H) (T : Type) [CommRing T] (x : Additive (WithConv (H →ₐ[ℤ] T))) (h' : H') :
    (Additive.toMul (precompAdd lv T x)) h' = (Additive.toMul x) (lv h') := rfl

theorem precompAdd_injective {H H' : Type} [CommRing H] [HopfAlgebra ℤ H] [CommRing H'] [HopfAlgebra ℤ H']
    (lv : H' →ₐc[ℤ] H) (hlv : Function.Surjective lv) (T : Type) [CommRing T] :
    Function.Injective (precompAdd lv T) := by
  intro x y h
  apply Additive.toMul.injective
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro a
  obtain ⟨a', rfl⟩ := hlv a
  have := congrArg (fun z => (Additive.toMul z) a') h
  simpa only [precompAdd_apply] using this

theorem exists_levelIncl_mono
    {H H' : Type} [CommRing H] [HopfAlgebra ℤ H] [CommRing H'] [HopfAlgebra ℤ H']
    (lv : H' →ₐc[ℤ] H) (hlv : Function.Surjective lv)
    (𝒥 𝒥' : Sheaf (smallFppfTopology specInt) Ab.{1})
    (sE : ∀ U : specInt.Fppf, 𝒥.1.obj (op U) ≃+ Additive (WithConv (H →ₐ[ℤ] Γ(U.left, ⊤))))
    (sNat : ∀ {U V : specInt.Fppf} (f : U ⟶ V) (s : 𝒥.1.obj (op V)) (h : H),
      (Additive.toMul (sE U (𝒥.1.map f.op s))) h = (Scheme.Γ.map f.left.op) ((Additive.toMul (sE V s)) h))
    (sE' : ∀ U : specInt.Fppf, 𝒥'.1.obj (op U) ≃+ Additive (WithConv (H' →ₐ[ℤ] Γ(U.left, ⊤))))
    (sNat' : ∀ {U V : specInt.Fppf} (f : U ⟶ V) (s : 𝒥'.1.obj (op V)) (h : H'),
      (Additive.toMul (sE' U (𝒥'.1.map f.op s))) h = (Scheme.Γ.map f.left.op) ((Additive.toMul (sE' V s)) h)) :
    ∃ incl : 𝒥 ⟶ 𝒥', Mono incl ∧
      ∀ (U : specInt.Fppf) (s : 𝒥.1.obj (op U)) (h' : H'),
        (Additive.toMul (sE' U (incl.hom.app (op U) s))) h' = (Additive.toMul (sE U s)) (lv h') := by

  let c : ∀ U : specInt.Fppf, 𝒥.1.obj (op U) →+ 𝒥'.1.obj (op U) := fun U =>
    (sE' U).symm.toAddMonoidHom.comp ((precompAdd lv Γ(U.left, ⊤)).comp (sE U).toAddMonoidHom)
  have hc : ∀ (U : specInt.Fppf) (s : 𝒥.1.obj (op U)) (h' : H'),
      (Additive.toMul (sE' U (c U s))) h' = (Additive.toMul (sE U s)) (lv h') := by
    intro U s h'
    simp only [c, AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply,
      precompAdd_apply]

  have hnat : ∀ {U V : specInt.Fppf} (f : U ⟶ V),
      𝒥.1.map f.op ≫ AddCommGrpCat.ofHom (c U) = AddCommGrpCat.ofHom (c V) ≫ 𝒥'.1.map f.op := by
    intro U V f
    ext s
    change c U (𝒥.1.map f.op s) = 𝒥'.1.map f.op (c V s)
    apply (sE' U).injective
    apply Additive.toMul.injective
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro h'
    change (Additive.toMul (sE' U (c U (𝒥.1.map f.op s)))) h' = (Additive.toMul (sE' U (𝒥'.1.map f.op (c V s)))) h'
    rw [hc, sNat, sNat', hc]
  let τ : 𝒥.obj ⟶ 𝒥'.obj := { app := fun U => AddCommGrpCat.ofHom (c U.unop), naturality := fun U V f => hnat f.unop }
  let incl : 𝒥 ⟶ 𝒥' := ObjectProperty.homMk τ
  have hτ : incl.hom = τ := rfl
  refine ⟨incl, ?_, ?_⟩
  ·
    haveI : ∀ U, Mono (τ.app U) := by
      intro U
      rw [AddCommGrpCat.mono_iff_injective]
      intro x y h
      exact (sE U.unop).injective (precompAdd_injective lv hlv _ ((sE' U.unop).symm.injective h))
    haveI : Mono incl.hom := by rw [hτ]; exact NatTrans.mono_of_mono_app τ
    exact Sheaf.Hom.mono_of_presheaf_mono (J := smallFppfTopology specInt) (A := Ab.{1}) incl
  · intro U s h'
    exact hc U s h'

end FltWs11.RoadB.SecD
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecA"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecA"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecA"

namespace FltWs11
namespace RoadB
namespace SecD

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite TensorProduct

local notation "ℤS" => Spec (CommRingCat.of ℤ)

theorem isProper_pullback_snd_of_closedImmersion_of_properAway
    {G : Scheme.{0}} (g : G ⟶ ℤS) {E : Scheme.{0}} (k : E ⟶ G) [IsClosedImmersion k]
    (P : Type) [CommRing P] [Algebra ℤ P]
    (hprop : IsProper (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ P)))))
    (S : Type) [CommRing S] [Algebra ℤ S] (φ : P →+* S) :
    IsProper (pullback.snd (k ≫ g) (Spec.map (CommRingCat.ofHom (algebraMap ℤ S)))) := by
  haveI := hprop

  have hfac : Spec.map (CommRingCat.ofHom (algebraMap ℤ S))
      = Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ P)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext_int _ _

  have h1 : IsProper (pullback.snd (k ≫ g) (Spec.map (CommRingCat.ofHom (algebraMap ℤ P)))) := by
    have hiso := pullbackRightPullbackFstIso_hom_snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ P))) k

    have : pullback.snd (k ≫ g) (Spec.map (CommRingCat.ofHom (algebraMap ℤ P)))
        = (pullbackRightPullbackFstIso g (Spec.map (CommRingCat.ofHom (algebraMap ℤ P))) k).inv ≫
          (pullback.snd k (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ P)))) ≫
            pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ P)))) := by
      rw [← hiso, Iso.inv_hom_id_assoc]
    rw [this, MorphismProperty.cancel_left_of_respectsIso (P := @IsProper)]
    infer_instance

  have h2 : IsProper (pullback.snd (pullback.snd (k ≫ g) (Spec.map (CommRingCat.ofHom (algebraMap ℤ P))))
      (Spec.map (CommRingCat.ofHom φ))) := inferInstance
  have hpaste := pullbackLeftPullbackSndIso_hom_snd (k ≫ g) (Spec.map (CommRingCat.ofHom (algebraMap ℤ P)))
    (Spec.map (CommRingCat.ofHom φ))

  have h3 : IsProper (pullback.snd (k ≫ g) (Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ P)))) := by
    have : pullback.snd (k ≫ g) (Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ P)))
        = (pullbackLeftPullbackSndIso (k ≫ g) (Spec.map (CommRingCat.ofHom (algebraMap ℤ P)))
            (Spec.map (CommRingCat.ofHom φ))).inv ≫
          pullback.snd (pullback.snd (k ≫ g) (Spec.map (CommRingCat.ofHom (algebraMap ℤ P)))) (Spec.map (CommRingCat.ofHom φ)) := by
      rw [← hpaste, Iso.inv_hom_id_assoc]
    rw [this, MorphismProperty.cancel_left_of_respectsIso (P := @IsProper)]
    exact h2

  rw [hfac]
  exact h3

end FltWs11.RoadB.SecD
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecA"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecA"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecA"

namespace FltWs11
namespace RoadB
namespace SecD

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite TensorProduct

local notation "ℤS" => Spec (CommRingCat.of ℤ)

theorem moduleFinite_baseChange_of_closedImmersion_of_properAway
    {G : Scheme.{0}} (g : G ⟶ ℤS) {E : Scheme.{0}} (k : E ⟶ G) [IsClosedImmersion k]
    (gE : E ⟶ ℤS) (hk : k ≫ g = gE) [IsAffineHom gE]
    (P : Type) [CommRing P] [Algebra ℤ P]
    (hprop : IsProper (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ P)))))
    (S : Type) [CommRing S] (φ : P →+* S)
    (H : Type) [CommRing H]
    (ι : H ≃+* Γ(E, ⊤)) :
    Module.Finite S (S ⊗[ℤ] H) := by
  subst hk
  letI algE : Algebra ℤ Γ(E, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv ≫ (k ≫ g).appTop).hom.toAlgebra

  let ι' : H ≃ₐ[ℤ] Γ(E, ⊤) := AlgEquiv.ofRingEquiv (f := ι) (fun z => by simp)
  let f := pullback.snd (k ≫ g) (Spec.map (CommRingCat.ofHom (algebraMap ℤ S)))
  letI algS : Algebra S Γ(pullback (k ≫ g) (Spec.map (CommRingCat.ofHom (algebraMap ℤ S))), ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appTop).hom.toAlgebra

  haveI : IsProper f := isProper_pullback_snd_of_closedImmersion_of_properAway g k P hprop S φ
  haveI : IsAffineHom f := inferInstance
  haveI : IsAffine E := isAffine_of_isAffineHom (k ≫ g)

  haveI hG3 : Module.Finite S Γ(pullback (k ≫ g) (Spec.map (CommRingCat.ofHom (algebraMap ℤ S))), ⊤) :=
    AlgebraicGeometry.moduleFinite_globalSections_of_isProper_of_isAffineHom f

  obtain ⟨e4, -⟩ := AlgebraicGeometry.exists_algEquiv_globalSections_pullback_spec_tensorProduct (k ≫ g) S
  haveI hG4 := Module.Finite.equiv (e4.symm.toLinearEquiv)

  have hfin := Module.Finite.equiv ((Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) ι'.symm).toLinearEquiv)
  exact hfin

end FltWs11.RoadB.SecD
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecA"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecA"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecA"

namespace FltWs11
namespace RoadB
namespace SecD

theorem isUnit_natCast_ratLocalizedAt (p ℓ : ℕ) (hp : p.Prime) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) :
    IsUnit ((p : ℤ) : ↥(GaloisRep.ratLocalizedAt ℓ)) := by
  have hcop : Nat.Coprime p ℓ := (Nat.coprime_primes hp hℓ).mpr (Ne.symm hℓp)
  have hmem : ((p : ℚ)⁻¹) ∈ GaloisRep.ratLocalizedAt ℓ := by
    change ((p : ℚ)⁻¹).den.Coprime ℓ
    rw [Rat.inv_natCast_den_of_pos hp.pos]
    exact hcop
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  refine ⟨⟨((p : ℤ) : ↥(GaloisRep.ratLocalizedAt ℓ)), ⟨(p : ℚ)⁻¹, hmem⟩, ?_, ?_⟩, rfl⟩
  · apply Subtype.ext
    change ((p : ℤ) : ℚ) * (p : ℚ)⁻¹ = 1
    push_cast
    exact mul_inv_cancel₀ hp0
  · apply Subtype.ext
    change (p : ℚ)⁻¹ * ((p : ℤ) : ℚ) = 1
    push_cast
    exact inv_mul_cancel₀ hp0

noncomputable def awayToRatLocalizedAt (p ℓ : ℕ) (hp : p.Prime) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) :
    Localization.Away (p : ℤ) →+* ↥(GaloisRep.ratLocalizedAt ℓ) :=
  Localization.awayLift (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ)) (p : ℤ)
    (by simpa using isUnit_natCast_ratLocalizedAt p ℓ hp hℓ hℓp)

end FltWs11.RoadB.SecD
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecA"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecA"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecA"

namespace FltWs11
namespace RoadB
namespace SecD

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

local notation "ℤS" => Spec (CommRingCat.of ℤ)

theorem isClosedImmersion_schemeKer_fst {p : ℕ} [Fact p.Prime] (N : ModularCurve.JZeroNeronIdentityComponent p) (n : ℕ) :
    IsClosedImmersion (pullback.fst (N.L.schemeNsmul n) (N.L.one (𝟙 ℤS)).1) := by
  haveI : IsSeparated N.g := N.separated
  haveI : IsClosedImmersion ((N.L.one (𝟙 ℤS)).1 ≫ N.g) := by
    rw [(N.L.one (𝟙 ℤS)).2]
    infer_instance
  haveI : IsClosedImmersion (N.L.one (𝟙 ℤS)).1 := IsClosedImmersion.of_comp (N.L.one (𝟙 ℤS)).1 N.g
  exact MorphismProperty.pullback_fst _ _ inferInstance

end FltWs11.RoadB.SecD
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecA"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecA"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecA"

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme NeronModelInfra GoodReductionJacobian ModularCurve

noncomputable section

namespace FltWs11
namespace RoadB

local notation "ℤS" => Spec (CommRingCat.of ℤ)
local notation "Qb" => AlgebraicClosure ℚ

variable (p q : ℕ) [Fact p.Prime] [Fact q.Prime]

theorem roadB_core_v10
    (hqp : q ≠ p) (A : ValuationSubring Qb) (hA : A.LiesOverPrime p)
    (N : JZeroNeronIdentityComponent p)

    (hAff : ∀ m, IsAffineHom (ιK p q N m ≫ N.g)) (hFlat : ∀ m, Flat (ιK p q N m ≫ N.g))
    (hLft : ∀ m, LocallyOfFiniteType (ιK p q N m ≫ N.g)) (hSep : ∀ m, IsSeparated (ιK p q N m ≫ N.g))

    (t : letI := heckeModuleBar p; ℕ → HeckeAlg) (φt : ℕ → SchemeHomOver N.g N.g)
    (eK : ∀ m, SchemeHomOver (ιK p q N m ≫ N.g) (ιK p q N m ≫ N.g))
    (ht : letI := heckeModuleBar p
      ∀ (m : ℕ) (x : JZero p), (q ^ m : ℤ) • x = 0 → (t m • x = x ↔ x ∈ eisensteinPrimaryTorsionBar p q m))
    (heK_idem : ∀ m, (eK m).1 ≫ (eK m).1 = (eK m).1)
    (hφt_pts : letI := heckeModuleBar p; ∀ (m : ℕ) (x : JZero p), (N.pts (t m • x)).1 = (N.pts x).1 ≫ (φt m).1)
    (heφ : ∀ m, (eK m).1 ≫ ιK p q N m = ιK p q N m ≫ (φt m).1)
    (hlevel : ∀ m, ιK p q N m ≫ (φt (m + 1)).1 = ιK p q N m ≫ (φt m).1)
    (heK_hom : ∀ (m : ℕ) (LK : RelativeGroupLaw ℤ (ιK p q N m ≫ N.g)),
      (∀ {T : Scheme.{0}} (s : T ⟶ ℤS) (x y : SchemeHomOver s (ιK p q N m ≫ N.g)),
        NeronModelInfra.schemeHomOverComp (LK.mul s x y) (⟨ιK p q N m, rfl⟩ : SchemeHomOver (ιK p q N m ≫ N.g) N.g) =
          N.L.mul s (NeronModelInfra.schemeHomOverComp x ⟨ιK p q N m, rfl⟩) (NeronModelInfra.schemeHomOverComp y ⟨ιK p q N m, rfl⟩)) →
      ∀ {T : Scheme.{0}} (s : T ⟶ ℤS) (x y : SchemeHomOver s (ιK p q N m ≫ N.g)),
        NeronModelInfra.schemeHomOverComp (LK.mul s x y) (eK m) =
          LK.mul s (NeronModelInfra.schemeHomOverComp x (eK m)) (NeronModelInfra.schemeHomOverComp y (eK m))) :

    ∃ (H : ℕ → Type) (_ : ∀ m, CommRing (H m)) (_ : ∀ m, HopfAlgebra ℤ (H m))
      (E : ℕ → Scheme.{0}) (gX : ∀ m, E m ⟶ ℤS) (i : ∀ m, E m ⟶ N.G) (j : ∀ m, E m ⟶ N.L.schemeKer (q ^ m))
      (LE : ∀ m, RelativeGroupLaw ℤ (gX m))
      (ePts : ∀ (m : ℕ) (T : Type) [CommRing T] [Algebra ℤ T],
        WithConv (H m →ₐ[ℤ] T) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ T))) (gX m))
      (genericPoints : ∀ m, WithConv (H m →ₐ[ℤ] Qb) ≃ ↥(eisensteinPrimaryTorsionBar p q m))
      (pFibrePoints : ∀ m, WithConv (H m →ₐ[ℤ] ↥A) ≃ ↥(toricEisensteinPrimaryPart p q A hA m))
      (𝒥 : ℕ → Sheaf (smallFppfTopology specInt) Ab.{1})
      (sE : ∀ (m : ℕ) (U : specInt.Fppf), (𝒥 m).1.obj (op U) ≃+ Additive (WithConv (H m →ₐ[ℤ] Γ(U.left, ⊤))))
      (levelMap : ∀ m, H (m + 1) →ₐc[ℤ] H m)
      (incl : ∀ m, 𝒥 m ⟶ 𝒥 (m + 1)) (Q : ℕ → Sheaf (smallFppfTopology specInt) Ab.{1})
      (proj : ∀ m, 𝒥 (m + 1) ⟶ Q m) (incl_proj : ∀ m, incl m ≫ proj m = 0),

      (∀ m, Algebra.FiniteType ℤ (H m)) ∧ (∀ m, Module.Flat ℤ (H m)) ∧
      (∀ (m ℓ : ℕ), ℓ.Prime → ℓ ≠ p →
        Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) (H m))) ∧

      (∀ m, i m ≫ N.g = gX m) ∧ (∀ m, IsClosedImmersion (i m)) ∧
      (∀ m, j m ≫ ιK p q N m = i m) ∧ (∀ m, IsClosedImmersion (j m)) ∧

      (∀ m (hj : j m ≫ ιK p q N m ≫ N.g = gX m) {T : Scheme.{0}} (s : T ⟶ ℤS) (x : SchemeHomOver s (ιK p q N m ≫ N.g)),
        NeronModelInfra.schemeHomOverComp x (eK m) = x ↔
          ∃ y : SchemeHomOver s (gX m), NeronModelInfra.schemeHomOverComp y (⟨j m, hj⟩ : SchemeHomOver (gX m) (ιK p q N m ≫ N.g)) = x) ∧
      (∀ m, IsAffineHom (gX m)) ∧ (∀ m, Flat (gX m)) ∧ (∀ m, LocallyOfFiniteType (gX m)) ∧
      (∀ m {T : Scheme.{0}} (t : T ⟶ ℤS) (x y : SchemeHomOver t (gX m)), (LE m).mul t x y = (LE m).mul t y x) ∧
      (∀ m (hi : i m ≫ N.g = gX m) {T : Scheme.{0}} (t : T ⟶ ℤS) (x y : SchemeHomOver t (gX m)),
        NeronModelInfra.schemeHomOverComp ((LE m).mul t x y) (⟨i m, hi⟩ : SchemeHomOver (gX m) N.g) =
          N.L.mul t (NeronModelInfra.schemeHomOverComp x ⟨i m, hi⟩) (NeronModelInfra.schemeHomOverComp y ⟨i m, hi⟩)) ∧
      (∀ m (x : JZero p), x ∈ eisensteinPrimaryTorsionBar p q m ↔
        ∃ y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ Qb))) (gX m), y.1 ≫ i m = (N.pts x).1) ∧
      (∀ (m : ℕ) (T : Type) [CommRing T] [Algebra ℤ T] (φ ψ : WithConv (H m →ₐ[ℤ] T)),
        ePts m T (φ * ψ) = (LE m).mul _ (ePts m T φ) (ePts m T ψ)) ∧
      (∀ (m : ℕ) (T T' : Type) [CommRing T] [Algebra ℤ T] [CommRing T'] [Algebra ℤ T']
          (σ : T →ₐ[ℤ] T') (φ : WithConv (H m →ₐ[ℤ] T)),
        (ePts m T' (.toConv (σ.comp φ.ofConv))).1 = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (ePts m T φ).1) ∧
      (∀ (m : ℕ) (T : Type) [CommRing T] (f g : WithConv (H m →ₐ[ℤ] T)), f * g = g * f) ∧

      (∀ m (φ : WithConv (H m →ₐ[ℤ] Qb)),
        (N.pts ((genericPoints m φ : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p)).1 = (ePts m Qb φ).1 ≫ i m) ∧
      (∀ m, ∀ f g : WithConv (H m →ₐ[ℤ] Qb), genericPoints m (f * g) = genericPoints m f + genericPoints m g) ∧
      (∀ m, ∀ σ : Qb ≃ₐ[ℚ] Qb, ∀ f g : WithConv (H m →ₐ[ℤ] Qb), (∀ h : H m, g h = σ (f h)) →
        ((genericPoints m g : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p)
          = σ • ((genericPoints m f : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p)) ∧

      (∀ m, ∀ f g : WithConv (H m →ₐ[ℤ] ↥A), pFibrePoints m (f * g) = pFibrePoints m f + pFibrePoints m g) ∧
      (∀ m, ∀ φ : WithConv (H m →ₐ[ℤ] ↥A), ∀ ψ : WithConv (H m →ₐ[ℤ] Qb), (∀ h : H m, ψ h = A.subtype (φ h)) →
        ((pFibrePoints m φ : ↥(toricEisensteinPrimaryPart p q A hA m)) : JZero p)
          = ((genericPoints m ψ : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p)) ∧

      (∀ (m : ℕ) {U V : specInt.Fppf} (f : U ⟶ V) (s : (𝒥 m).1.obj (op V)) (h : H m),
        (Additive.toMul (sE m U ((𝒥 m).1.map f.op s))) h = (Scheme.Γ.map f.left.op) ((Additive.toMul (sE m V s)) h)) ∧
      (∀ m, Function.Surjective (levelMap m)) ∧
      (∀ m (φ : WithConv (H m →ₐ[ℤ] Qb)),
        ((genericPoints (m + 1) (WithConv.toConv ((WithConv.ofConv φ).comp (levelMap m : H (m + 1) →ₐ[ℤ] H m)))
            : ↥(eisensteinPrimaryTorsionBar p q (m + 1))) : JZero p)
          = ((genericPoints m φ : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p)) ∧
      (∀ (m : ℕ) (U : specInt.Fppf) (s : (𝒥 m).1.obj (op U)) (h' : H (m + 1)),
        (Additive.toMul (sE (m + 1) U ((incl m).hom.app (op U) s))) h' = (Additive.toMul (sE m U s)) (levelMap m h')) ∧
      (∀ m, Mono (incl m)) ∧
      (∀ m, (ShortComplex.mk (incl m) (proj m) (incl_proj m)).ShortExact) := by
  classical
  letI := heckeModuleBar p

  have hK := fun m => GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_schemeKer_forall_mem_torsionSubset_iff
    N.L (fun t x y => N.comm t x y) (q ^ m)
  choose LK hLKstr hLKcomm hLKhom hLKinj hLKpts using hK

  haveI := hAff; haveI := hFlat; haveI := hLft; haveI := hSep
  have hE := fun m => GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_image_of_idempotent
    (LK m) (hLKcomm m) (eK m) (heK_hom m (LK m) (hLKhom m)) (heK_idem m)
  choose E j LE hj_closed hE_aff hE_flat hE_lft hE_comm hj_hom hE_pts using hE

  haveI := hE_aff; haveI := hE_flat; haveI := hE_lft
  have hH := fun m =>
    GoodReductionJacobian.RelativeGroupLaw.exists_hopfAlgebra_algEquiv_globalSections_of_isAffineHom (LE m) (hE_comm m)
  choose H instCR instHA hft hflat hcocomm iso ePts hiso hconv hnat using hH
  letI := instCR; letI := instHA
  have hflat' : ∀ m, Module.Flat ℤ (H m) := fun m => by
    convert hflat m using 2 <;> first | rfl | exact Subsingleton.elim _ _

  have ff_finite : ∀ (m ℓ : ℕ), ℓ.Prime → ℓ ≠ p →
      Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) (H m)) := by
    intro m ℓ hℓ hℓp
    haveI := hj_closed m; haveI := hE_aff m
    haveI : IsClosedImmersion (ιK p q N m) := SecD.isClosedImmersion_schemeKer_fst N (q ^ m)
    letI : Algebra ℤ Γ(E m, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv ≫ (j m ≫ ιK p q N m ≫ N.g).appTop).hom.toAlgebra
    exact SecD.moduleFinite_baseChange_of_closedImmersion_of_properAway N.g (j m ≫ ιK p q N m)
      (j m ≫ ιK p q N m ≫ N.g) (Category.assoc _ _ _) (Localization.Away (p : ℤ)) N.proper_away
      (↥(GaloisRep.ratLocalizedAt ℓ)) (SecD.awayToRatLocalizedAt p ℓ Fact.out hℓ hℓp) (H m) (iso m).toRingEquiv

  haveI : ∀ m, Mono (j m) := fun m => by haveI := hj_closed m; infer_instance
  let gpm := fun m => SecA.gp N (ιK p q N m) (j m) (ePts m)
  have hgp_inj : ∀ m, Function.Injective (gpm m) := fun m =>
    SecA.gp_injective N (ιK p q N m) (j m) (ePts m) (hLKinj m)
  have hgp_mem : ∀ m φ, gpm m φ ∈ eisensteinPrimaryTorsionBar p q m := fun m φ =>
    SecA.gp_mem q N m (ιK p q N m) (j m) (ePts m) (hLKpts m) (eK m) (hE_pts m) (t m) (ht m) (φt m) (hφt_pts m) (heφ m) φ
  have hgp_surj : ∀ m, ∀ y ∈ eisensteinPrimaryTorsionBar p q m, ∃ φ, gpm m φ = y := fun m y hy =>
    SecA.gp_surjOn q N m (ιK p q N m) (j m) (ePts m) (hLKpts m) (hLKinj m) (eK m) (hE_pts m) (t m) (ht m) (φt m)
      (hφt_pts m) (heφ m) y hy
  let genericPoints := fun m => SecA.genericEquiv q N m (ιK p q N m) (j m) (ePts m) (hgp_inj m) (hgp_mem m) (hgp_surj m)
  have hconvQ : ∀ m (f g : WithConv (H m →ₐ[ℤ] Qb)), gpm m (f * g) = gpm m f + gpm m g := fun m f g =>
    SecA.gp_mul N (ιK p q N m) (j m) (ePts m) (LK m) (LE m) (hconv m) (hj_hom m) (hLKhom m) f g

  have hmemT : ∀ m (φ : WithConv (H m →ₐ[ℤ] ↥A)), SecB.pFibreMap p A (gpm m) φ ∈ jZeroToricTorsion p A (q ^ m) :=
    fun m φ => SecB.pFibreMap_mem_jZeroToricTorsion p q hqp A hA N m (j m ≫ ιK p q N m ≫ N.g) (j m ≫ ιK p q N m)
      (by rw [Category.assoc]) (ePts m) (hnat m) (gpm m) (fun ψ => SecA.pts_gp_val N (ιK p q N m) (j m) (ePts m) ψ)
      (fun ψ => (hgp_mem m ψ).1) φ
  have hsurjB : ∀ m, ∀ y ∈ toricEisensteinPrimaryPart p q A hA m, ∃ φ : WithConv (H m →ₐ[ℤ] ↥A),
      SecB.pFibreMap p A (gpm m) φ = y := fun m y hy => by
    haveI := hSep m
    exact SecB.pFibreMap_surjOn p q hqp A hA N m (ιK p q N m) (hLKinj m) (hLKpts m) (eK m) (j m) (hE_pts m) (t m)
      (fun x hx => ht m x ((Submodule.mem_torsionBy_iff _ _).mp hx)) (fun x => SecA.he_gen_of N (ιK p q N m) (eK m) (t m) (φt m) (hφt_pts m) (heφ m) x)
      (ePts m) (hnat m) (gpm m) (fun ψ => SecA.pts_gp_val N (ιK p q N m) (j m) (ePts m) ψ) y hy
  let pFibrePoints := fun m => SecB.pFibreEquiv p q A hA m (gpm m) (hgp_inj m) (hgp_mem m) (hmemT m) (hsurjB m)

  have hJ := fun m => SecD.exists_pointsSheaf (LE m) (hE_comm m) (H m) (ePts m) (hconv m)
  choose 𝒥 sE sNat using hJ

  have hUm := fun m => by
    haveI := hj_closed m; haveI := hj_closed (m + 1)
    exact SecC.exists_levelHom q N m (hLKpts (m + 1)) (hLKpts m) (eK m) (eK (m + 1)) (φt m) (φt (m + 1)) (heφ m) (heφ (m + 1))
      (hlevel m) (j m) (j (m + 1)) (hE_pts m) (hE_pts (m + 1))
  choose u hu1 hu_closed using hUm

  have hGL3 := fun m =>
    GoodReductionJacobian.RelativeGroupLaw.exists_bialgHom_of_schemeHomOver_of_forall_mul
      (LE (m + 1)) (LE m) (u m)
      (SecC.hu_of N (ιK p q N m) (ιK p q N (m + 1)) (j m) (j (m + 1)) (LK m) (LK (m + 1)) (LE m) (LE (m + 1))
        (hj_hom m) (hLKhom m) (hj_hom (m + 1)) (hLKhom (m + 1)) (hLKinj (m + 1)) (u m) (hu1 m))
      (H (m + 1)) (H m) (iso (m + 1)) (iso m) (ePts (m + 1)) (ePts m)
      (hiso (m + 1)) (hiso m) (hconv (m + 1)) (hconv m)
  choose levelMap hlv_iso hlv_pts hlv_surj using hGL3
  have hlv_surj' : ∀ m, Function.Surjective (levelMap m) := fun m => hlv_surj m (hu_closed m)

  have hD3 := fun m => SecD.exists_levelIncl_mono (levelMap m) (hlv_surj' m) (𝒥 m) (𝒥 (m + 1)) (sE m) (sNat m)
    (sE (m + 1)) (sNat (m + 1))
  choose incl hmono hincl using hD3

  obtain ⟨Qs, proj, incl_proj, hses⟩ := SecD.exists_cokernel_shortExact 𝒥 incl hmono
  have hi : ∀ m, (j m ≫ ιK p q N m) ≫ N.g = j m ≫ ιK p q N m ≫ N.g := fun m => Category.assoc _ _ _
  refine ⟨H, instCR, instHA, E, fun m => j m ≫ ιK p q N m ≫ N.g, fun m => j m ≫ ιK p q N m, j, LE, ePts,
    genericPoints, pFibrePoints, 𝒥, sE, levelMap, incl, Qs, proj, incl_proj,
    hft, hflat', ff_finite, hi, ?_, fun m => rfl, hj_closed, fun m hj => hE_pts m, hE_aff, hE_flat, hE_lft,
    fun m => hE_comm m, ?_, ?_, hconv, hnat, ?_,
    ?_, ?_, ?_, ?_, ?_, fun m => sNat m, hlv_surj', ?_, hincl, hmono, hses⟩
  ·
    intro m
    haveI := hj_closed m
    haveI : IsClosedImmersion (ιK p q N m) := SecD.isClosedImmersion_schemeKer_fst N (q ^ m)
    infer_instance
  ·
    intro m hi' T t x y
    have h1 : ∀ z : SchemeHomOver t (j m ≫ ιK p q N m ≫ N.g),
        NeronModelInfra.schemeHomOverComp z (⟨j m ≫ ιK p q N m, hi'⟩ : SchemeHomOver (j m ≫ ιK p q N m ≫ N.g) N.g)
          = NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp z
              (⟨j m, rfl⟩ : SchemeHomOver (j m ≫ ιK p q N m ≫ N.g) (ιK p q N m ≫ N.g)))
              (⟨ιK p q N m, rfl⟩ : SchemeHomOver (ιK p q N m ≫ N.g) N.g) := by
      intro z
      apply Subtype.ext
      change z.1 ≫ (j m ≫ ιK p q N m) = (z.1 ≫ j m) ≫ ιK p q N m
      rw [Category.assoc]
    rw [h1, h1, h1, hj_hom, hLKhom]
  ·
    intro m x
    constructor
    · intro hx
      obtain ⟨φ, hφ⟩ := hgp_surj m x hx
      refine ⟨ePts m Qb φ, ?_⟩
      rw [← hφ]
      exact (SecA.pts_gp_val N (ιK p q N m) (j m) (ePts m) φ).symm
    · rintro ⟨y, hy⟩
      have hφ : gpm m ((ePts m Qb).symm y) = x := by
        apply N.pts.injective
        apply Subtype.ext
        rw [SecA.pts_gp_val, Equiv.apply_symm_apply, hy]
      rw [← hφ]
      exact hgp_mem m _
  ·
    intro m T _ f g
    exact SecD.convMul_comm_of_points (LE m) (hE_comm m) (ePts m) (hconv m) T f g
  ·
    intro m φ
    exact SecA.pts_gp_val N (ιK p q N m) (j m) (ePts m) φ
  · intro m f g
    apply Subtype.ext
    exact hconvQ m f g
  · intro m σ f g hfg
    exact SecA.gp_galois N (ιK p q N m) (j m) (ePts m) (hnat m) σ f g hfg
  · intro m f g
    exact SecB.pFibreEquiv_mul p q A hA m (gpm m) (hgp_inj m) (hgp_mem m) (hmemT m) (hsurjB m) (hconvQ m) f g
  · intro m φ ψ hψ
    exact SecB.pFibreMap_eq_of_forall p A (gpm m) φ ψ hψ
  ·
    intro m φ
    apply N.pts.injective
    apply Subtype.ext
    change (N.pts (gpm (m + 1) _)).1 = (N.pts (gpm m φ)).1
    rw [SecA.pts_gp_val, SecA.pts_gp_val, hlv_pts m Qb φ, Category.assoc, hu1 m]

end FltWs11.RoadB
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecA"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecA"

end
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11 P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecB P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.FltWs11.RoadB.SecA"

theorem solution
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hqp : q ≠ p) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (N : JZeroNeronIdentityComponent p)

    (hAff : ∀ m, IsAffineHom (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)) (hFlat : ∀ m, Flat (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g))
    (hLft : ∀ m, LocallyOfFiniteType (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)) (hSep : ∀ m, IsSeparated (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g))

    (t : letI := heckeModuleBar p; ℕ → HeckeAlg) (φt : ℕ → SchemeHomOver N.g N.g)
    (eK : ∀ m, SchemeHomOver (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g) (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g))
    (ht : letI := heckeModuleBar p
      ∀ (m : ℕ) (x : JZero p), (q ^ m : ℤ) • x = 0 → (t m • x = x ↔ x ∈ eisensteinPrimaryTorsionBar p q m))
    (heK_idem : ∀ m, (eK m).1 ≫ (eK m).1 = (eK m).1)
    (hφt_pts : letI := heckeModuleBar p; ∀ (m : ℕ) (x : JZero p), (N.pts (t m • x)).1 = (N.pts x).1 ≫ (φt m).1)
    (heφ : ∀ m, (eK m).1 ≫ pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 = pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ (φt m).1)
    (hlevel : ∀ m, pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ (φt (m + 1)).1 = pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ (φt m).1)
    (heK_hom : ∀ (m : ℕ) (LK : RelativeGroupLaw ℤ (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)),
      (∀ {T : Scheme.{0}} (s : T ⟶ (Spec (CommRingCat.of ℤ))) (x y : SchemeHomOver s (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)),
        NeronModelInfra.schemeHomOverComp (LK.mul s x y) (⟨pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1, rfl⟩ : SchemeHomOver (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g) N.g) =
          N.L.mul s (NeronModelInfra.schemeHomOverComp x ⟨pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1, rfl⟩) (NeronModelInfra.schemeHomOverComp y ⟨pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1, rfl⟩)) →
      ∀ {T : Scheme.{0}} (s : T ⟶ (Spec (CommRingCat.of ℤ))) (x y : SchemeHomOver s (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)),
        NeronModelInfra.schemeHomOverComp (LK.mul s x y) (eK m) =
          LK.mul s (NeronModelInfra.schemeHomOverComp x (eK m)) (NeronModelInfra.schemeHomOverComp y (eK m))) :
    ∃ (H : ℕ → Type) (_ : ∀ m, CommRing (H m)) (_ : ∀ m, HopfAlgebra ℤ (H m))
      (E : ℕ → Scheme.{0}) (gX : ∀ m, E m ⟶ (Spec (CommRingCat.of ℤ))) (i : ∀ m, E m ⟶ N.G) (j : ∀ m, E m ⟶ N.L.schemeKer (q ^ m))
      (LE : ∀ m, RelativeGroupLaw ℤ (gX m))
      (ePts : ∀ (m : ℕ) (T : Type) [CommRing T] [Algebra ℤ T],
        WithConv (H m →ₐ[ℤ] T) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ T))) (gX m))
      (genericPoints : ∀ m, WithConv (H m →ₐ[ℤ] (AlgebraicClosure ℚ)) ≃ ↥(eisensteinPrimaryTorsionBar p q m))
      (pFibrePoints : ∀ m, WithConv (H m →ₐ[ℤ] ↥A) ≃ ↥(toricEisensteinPrimaryPart p q A hA m))
      (𝒥 : ℕ → Sheaf (smallFppfTopology specInt) Ab.{1})
      (sE : ∀ (m : ℕ) (U : specInt.Fppf), (𝒥 m).1.obj (op U) ≃+ Additive (WithConv (H m →ₐ[ℤ] Γ(U.left, ⊤))))
      (levelMap : ∀ m, H (m + 1) →ₐc[ℤ] H m)
      (incl : ∀ m, 𝒥 m ⟶ 𝒥 (m + 1)) (Q : ℕ → Sheaf (smallFppfTopology specInt) Ab.{1})
      (proj : ∀ m, 𝒥 (m + 1) ⟶ Q m) (incl_proj : ∀ m, incl m ≫ proj m = 0),

      (∀ m, Algebra.FiniteType ℤ (H m)) ∧ (∀ m, Module.Flat ℤ (H m)) ∧
      (∀ (m ℓ : ℕ), ℓ.Prime → ℓ ≠ p →
        Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) (H m))) ∧

      (∀ m, i m ≫ N.g = gX m) ∧ (∀ m, IsClosedImmersion (i m)) ∧
      (∀ m, j m ≫ pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 = i m) ∧ (∀ m, IsClosedImmersion (j m)) ∧

      (∀ m (hj : j m ≫ pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g = gX m) {T : Scheme.{0}} (s : T ⟶ (Spec (CommRingCat.of ℤ))) (x : SchemeHomOver s (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)),
        NeronModelInfra.schemeHomOverComp x (eK m) = x ↔
          ∃ y : SchemeHomOver s (gX m), NeronModelInfra.schemeHomOverComp y (⟨j m, hj⟩ : SchemeHomOver (gX m) (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)) = x) ∧
      (∀ m, IsAffineHom (gX m)) ∧ (∀ m, Flat (gX m)) ∧ (∀ m, LocallyOfFiniteType (gX m)) ∧
      (∀ m {T : Scheme.{0}} (t : T ⟶ (Spec (CommRingCat.of ℤ))) (x y : SchemeHomOver t (gX m)), (LE m).mul t x y = (LE m).mul t y x) ∧
      (∀ m (hi : i m ≫ N.g = gX m) {T : Scheme.{0}} (t : T ⟶ (Spec (CommRingCat.of ℤ))) (x y : SchemeHomOver t (gX m)),
        NeronModelInfra.schemeHomOverComp ((LE m).mul t x y) (⟨i m, hi⟩ : SchemeHomOver (gX m) N.g) =
          N.L.mul t (NeronModelInfra.schemeHomOverComp x ⟨i m, hi⟩) (NeronModelInfra.schemeHomOverComp y ⟨i m, hi⟩)) ∧
      (∀ m (x : JZero p), x ∈ eisensteinPrimaryTorsionBar p q m ↔
        ∃ y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) (gX m), y.1 ≫ i m = (N.pts x).1) ∧
      (∀ (m : ℕ) (T : Type) [CommRing T] [Algebra ℤ T] (φ ψ : WithConv (H m →ₐ[ℤ] T)),
        ePts m T (φ * ψ) = (LE m).mul _ (ePts m T φ) (ePts m T ψ)) ∧
      (∀ (m : ℕ) (T T' : Type) [CommRing T] [Algebra ℤ T] [CommRing T'] [Algebra ℤ T']
          (σ : T →ₐ[ℤ] T') (φ : WithConv (H m →ₐ[ℤ] T)),
        (ePts m T' (.toConv (σ.comp φ.ofConv))).1 = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (ePts m T φ).1) ∧
      (∀ (m : ℕ) (T : Type) [CommRing T] (f g : WithConv (H m →ₐ[ℤ] T)), f * g = g * f) ∧

      (∀ m (φ : WithConv (H m →ₐ[ℤ] (AlgebraicClosure ℚ))),
        (N.pts ((genericPoints m φ : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p)).1 = (ePts m (AlgebraicClosure ℚ) φ).1 ≫ i m) ∧
      (∀ m, ∀ f g : WithConv (H m →ₐ[ℤ] (AlgebraicClosure ℚ)), genericPoints m (f * g) = genericPoints m f + genericPoints m g) ∧
      (∀ m, ∀ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), ∀ f g : WithConv (H m →ₐ[ℤ] (AlgebraicClosure ℚ)), (∀ h : H m, g h = σ (f h)) →
        ((genericPoints m g : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p)
          = σ • ((genericPoints m f : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p)) ∧

      (∀ m, ∀ f g : WithConv (H m →ₐ[ℤ] ↥A), pFibrePoints m (f * g) = pFibrePoints m f + pFibrePoints m g) ∧
      (∀ m, ∀ φ : WithConv (H m →ₐ[ℤ] ↥A), ∀ ψ : WithConv (H m →ₐ[ℤ] (AlgebraicClosure ℚ)), (∀ h : H m, ψ h = A.subtype (φ h)) →
        ((pFibrePoints m φ : ↥(toricEisensteinPrimaryPart p q A hA m)) : JZero p)
          = ((genericPoints m ψ : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p)) ∧

      (∀ (m : ℕ) {U V : specInt.Fppf} (f : U ⟶ V) (s : (𝒥 m).1.obj (op V)) (h : H m),
        (Additive.toMul (sE m U ((𝒥 m).1.map f.op s))) h = (Scheme.Γ.map f.left.op) ((Additive.toMul (sE m V s)) h)) ∧
      (∀ m, Function.Surjective (levelMap m)) ∧
      (∀ m (φ : WithConv (H m →ₐ[ℤ] (AlgebraicClosure ℚ))),
        ((genericPoints (m + 1) (WithConv.toConv ((WithConv.ofConv φ).comp (levelMap m : H (m + 1) →ₐ[ℤ] H m)))
            : ↥(eisensteinPrimaryTorsionBar p q (m + 1))) : JZero p)
          = ((genericPoints m φ : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p)) ∧
      (∀ (m : ℕ) (U : specInt.Fppf) (s : (𝒥 m).1.obj (op U)) (h' : H (m + 1)),
        (Additive.toMul (sE (m + 1) U ((incl m).hom.app (op U) s))) h' = (Additive.toMul (sE m U s)) (levelMap m h')) ∧
      (∀ m, Mono (incl m)) ∧
      (∀ m, (ShortComplex.mk (incl m) (proj m) (incl_proj m)).ShortExact) :=
  FltWs11.RoadB.roadB_core_v10 p q hqp A hA N hAff hFlat hLft hSep t φt eK ht heK_idem hφt_pts heφ hlevel heK_hom

end S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent
end P2MW
export P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent (solution)
