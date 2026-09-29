-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.exists_twoSidedPool_of_oneSided
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/193ede51-4a0e-551b-8ce5-7e633544c33f

import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_exists_twoSidedPool_of_oneSided
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicCurve NeronModelInfra GoodReductionJacobian"
open AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve TensorProduct
p2m_open "ModularCurve P2MW.S_ModularCurve_DRModelPackageLevel_exists_twoSidedPool_of_oneSided.ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "DRModelPackageLevel IgusaScheme"
namespace DRModelPackageLevel
p2m_export "ModularCurve.DRModelPackageLevel" "isProper εzero εinf flat εzero_mem_smoothLocus w w_over smoothLocus w_sections smoothLocus_maximal w_invol"
p2m_open "ModularCurve.DRModelPackageLevel ModularCurve"

namespace TwoSidedAux

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime] {hqN : ¬ q ∣ N₀} (𝔓 : DRModelPackageLevel N₀ q hqN) (f : R q)

local notation "L" => Localization.Away f
local notation "XL" => pullback (toBase N₀ q) (specMap (R q) (Localization.Away f))
local notation "bcL" => baseChange (R q) (toBase N₀ q) (Localization.Away f)

abbrev wL : XL ⟶ XL := curveChange 𝔓.w.hom 𝔓.w_over (specMap (R q) (Localization.Away f))

@[reassoc] theorem wL_fst : wL 𝔓 f ≫ pullback.fst _ _ = pullback.fst _ _ ≫ 𝔓.w.hom := by
  unfold wL curveChange; rw [pullback.lift_fst]

@[reassoc] theorem wL_snd : wL 𝔓 f ≫ bcL = bcL := curveChange_snd _ _ _

@[reassoc] theorem wL_wL : wL 𝔓 f ≫ wL 𝔓 f = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, wL_fst, wL_fst_assoc, 𝔓.w_invol, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, wL_snd, wL_snd, Category.id_comp]

theorem wL_base_wL_base (x : ↥XL) : (wL 𝔓 f).base ((wL 𝔓 f).base x) = x := by
  rw [← Scheme.Hom.comp_apply, wL_wL]; rfl

theorem wL_base_injective : Function.Injective (wL 𝔓 f).base :=
  Function.LeftInverse.injective (wL_base_wL_base 𝔓 f)

theorem εinf_wL : (sectionBaseChange (Localization.Away f) 𝔓.εinf).1 ≫ wL 𝔓 f =
    (sectionBaseChange (Localization.Away f) 𝔓.εzero).1 := by
  apply pullback.hom_ext
  · rw [Category.assoc, wL_fst, ← Category.assoc, sectionBaseChange_coe_fst, sectionBaseChange_coe_fst, Category.assoc,
      𝔓.w_sections]
  · rw [Category.assoc, wL_snd]
    exact ((sectionBaseChange (Localization.Away f) 𝔓.εinf).2).trans ((sectionBaseChange (Localization.Away f) 𝔓.εzero).2).symm

theorem range_εzero_eq : Set.range (sectionBaseChange (Localization.Away f) 𝔓.εzero).1.base =
    (wL 𝔓 f).base '' Set.range (sectionBaseChange (Localization.Away f) 𝔓.εinf).1.base := by
  rw [← Set.range_comp, ← εinf_wL]; rfl

theorem w_preimage_smoothLocus_le : 𝔓.w.hom ⁻¹ᵁ 𝔓.smoothLocus ≤ 𝔓.smoothLocus := by
  apply 𝔓.smoothLocus_maximal
  have e : (𝔓.w.hom ⁻¹ᵁ 𝔓.smoothLocus).ι ≫ toBase N₀ q = (𝔓.w.hom ∣_ 𝔓.smoothLocus) ≫ (𝔓.smoothLocus.ι ≫ toBase N₀ q) := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, 𝔓.w_over]
  rw [e]
  infer_instance

theorem w_base_mem_smoothLocus {x : ↥(X N₀ q)} (hx : x ∈ (𝔓.smoothLocus : Set ↥(X N₀ q))) :
    𝔓.w.hom.base x ∈ (𝔓.smoothLocus : Set ↥(X N₀ q)) := by
  apply w_preimage_smoothLocus_le 𝔓
  show 𝔓.w.hom.base (𝔓.w.hom.base x) ∈ (𝔓.smoothLocus : Set ↥(X N₀ q))
  rw [← Scheme.Hom.comp_apply, 𝔓.w_invol]; exact hx

theorem wL_base_mem_preimage_smoothLocus {x : ↥XL}
    (hx : x ∈ ((pullback.fst (toBase N₀ q) (specMap (R q) (Localization.Away f)) ⁻¹ᵁ 𝔓.smoothLocus : (XL).Opens) : Set ↥XL)) :
    (wL 𝔓 f).base x ∈ ((pullback.fst (toBase N₀ q) (specMap (R q) (Localization.Away f)) ⁻¹ᵁ 𝔓.smoothLocus : (XL).Opens) : Set ↥XL) := by
  show (pullback.fst (toBase N₀ q) (specMap (R q) (Localization.Away f))).base ((wL 𝔓 f).base x) ∈ (𝔓.smoothLocus : Set ↥(X N₀ q))
  rw [← Scheme.Hom.comp_apply, wL_fst, Scheme.Hom.comp_apply]
  exact w_base_mem_smoothLocus 𝔓 hx

theorem isClosedImmersion_εzero : IsClosedImmersion (sectionBaseChange (Localization.Away f) 𝔓.εzero).1 := by
  haveI := 𝔓.isProper
  have : IsClosedImmersion ((sectionBaseChange (Localization.Away f) 𝔓.εzero).1 ≫ bcL) := by
    rw [(sectionBaseChange (Localization.Away f) 𝔓.εzero).2]; infer_instance
  exact .of_comp _ (bcL)

theorem range_εzero_subset : Set.range (sectionBaseChange (Localization.Away f) 𝔓.εzero).1.base ⊆
    ((pullback.fst (toBase N₀ q) (specMap (R q) (Localization.Away f)) ⁻¹ᵁ 𝔓.smoothLocus : (XL).Opens) : Set ↥XL) := by
  rintro _ ⟨t, rfl⟩
  show (pullback.fst (toBase N₀ q) (specMap (R q) (Localization.Away f))).base ((sectionBaseChange (Localization.Away f) 𝔓.εzero).1.base t) ∈ (𝔓.smoothLocus : Set ↥(X N₀ q))
  rw [← Scheme.Hom.comp_apply, sectionBaseChange_coe_fst, Scheme.Hom.comp_apply]
  exact 𝔓.εzero_mem_smoothLocus ⟨_, rfl⟩

theorem eq_sectionFibrePoint_of_mem {k : Type} [Field k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
    (γ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (Localization.Away f)))) (bcL)) (y : ↥(pullback (bcL) s))
    (hy : (pullback.fst (bcL) s).base y ∈ Set.range γ.1.base) :
    y = (sectionFibrePoint γ s).1.base (IsLocalRing.closedPoint k) := by

  have hrange := Scheme.Pullback.range_map (𝟙 (Spec (CommRingCat.of (Localization.Away f)))) s (bcL) s γ.1 (𝟙 _) (𝟙 _)
    (by rw [γ.2, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])
  have hy' : y ∈ Set.range (pullback.map (𝟙 (Spec (CommRingCat.of (Localization.Away f)))) s (bcL) s γ.1 (𝟙 _) (𝟙 _)
      (by rw [γ.2, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])).base := by
    rw [hrange]
    exact ⟨hy, by simp⟩
  obtain ⟨t, rfl⟩ := hy'

  have ht : t = (pullback.lift s (𝟙 _) (by simp)).base (IsLocalRing.closedPoint k) := by
    have hid : pullback.snd (𝟙 (Spec (CommRingCat.of (Localization.Away f)))) s ≫ pullback.lift s (𝟙 _) (by simp) = 𝟙 _ := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, Category.id_comp, ← pullback.condition, Category.comp_id]
      · rw [Category.assoc, pullback.lift_snd, Category.id_comp, Category.comp_id]
    have h1 : t = (pullback.lift s (𝟙 _) (by simp)).base ((pullback.snd (𝟙 (Spec (CommRingCat.of (Localization.Away f)))) s).base t) := by
      rw [← Scheme.Hom.comp_apply, hid]; rfl
    rw [h1, Subsingleton.elim ((pullback.snd (𝟙 _) s).base t) (IsLocalRing.closedPoint k)]
  have hm : pullback.lift s (𝟙 _) (by simp) ≫ pullback.map (𝟙 (Spec (CommRingCat.of (Localization.Away f)))) s (bcL) s γ.1
      (𝟙 _) (𝟙 _) (by rw [γ.2, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp]) = (sectionFibrePoint γ s).1 := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      exact (pullback.lift_fst _ _ _).symm
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.id_comp]
      exact (sectionFibrePoint γ s).2.symm
  rw [ht, ← Scheme.Hom.comp_apply, hm]

abbrev wLs {k : Type} [Field k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f))) :
    pullback (bcL) s ⟶ pullback (bcL) s :=
  pullback.map (bcL) s (bcL) s (wL 𝔓 f) (𝟙 _) (𝟙 _)
    ((Category.comp_id _).trans (curveChange_snd _ _ _).symm) ((Category.comp_id _).trans (Category.id_comp _).symm)

theorem wLs_fst {k : Type} [Field k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f))) :
    wLs 𝔓 f s ≫ pullback.fst _ _ = pullback.fst _ _ ≫ wL 𝔓 f := pullback.lift_fst _ _ _

theorem wLs_wLs {k : Type} [Field k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f))) :
    wLs 𝔓 f s ≫ wLs 𝔓 f s = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, wLs_fst, ← Category.assoc, wLs_fst, Category.assoc, wL_wL, Category.comp_id, Category.id_comp]
  · unfold wLs
    rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, Category.comp_id, Category.comp_id,
      Category.id_comp]

theorem wLs_base_wLs_base {k : Type} [Field k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
    (y : ↥(pullback (bcL) s)) : (wLs 𝔓 f s).base ((wLs 𝔓 f s).base y) = y := by
  rw [← Scheme.Hom.comp_apply, wLs_wLs]; rfl

end TwoSidedAux

namespace TwoSidedAux

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime] {hqN : ¬ q ∣ N₀} (𝔓 : DRModelPackageLevel N₀ q hqN) (f : R q)

scoped instance isIso_wL : IsIso (wL 𝔓 f) := ⟨⟨wL 𝔓 f, wL_wL 𝔓 f, wL_wL 𝔓 f⟩⟩

theorem range_comp_wL {Y : Scheme.{0}} (g : Y ⟶ pullback (toBase N₀ q) (specMap (R q) (Localization.Away f))) :
    Set.range (g ≫ wL 𝔓 f).base = (wL 𝔓 f).base '' Set.range g.base := by
  rw [← Set.range_comp]; rfl

theorem wLs_fst_base {k : Type} [Field k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
    (y : ↥(pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s)) :
    (pullback.fst (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s).base ((wLs 𝔓 f s).base y) =
      (wL 𝔓 f).base ((pullback.fst (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s).base y) := by
  rw [← Scheme.Hom.comp_apply, wLs_fst, Scheme.Hom.comp_apply]

section Far

variable {M : ℕ} (B : Fin M → Type) [∀ i, CommRing (B i)] [∀ i, Algebra (Localization.Away f) (B i)]

def farB : Fin (M + 1) → Type := Fin.cases (Localization.Away f) B

scoped instance farCommRing : ∀ i, CommRing (farB f B i) :=
  Fin.cases (inferInstanceAs (CommRing (Localization.Away f))) (fun j => inferInstanceAs (CommRing (B j)))

scoped instance farAlgebra : ∀ i, Algebra (Localization.Away f) (farB f B i) :=
  Fin.cases (inferInstanceAs (Algebra (Localization.Away f) (Localization.Away f)))
    (fun j => inferInstanceAs (Algebra (Localization.Away f) (B j)))

theorem farFinite [∀ i, Module.Finite (Localization.Away f) (B i)] : ∀ i, Module.Finite (Localization.Away f) (farB f B i) :=
  Fin.cases (inferInstanceAs (Module.Finite (Localization.Away f) (Localization.Away f)))
    (fun j => inferInstanceAs (Module.Finite (Localization.Away f) (B j)))

theorem farEtale [∀ i, Algebra.Etale (Localization.Away f) (B i)] : ∀ i, Algebra.Etale (Localization.Away f) (farB f B i) :=
  Fin.cases (inferInstanceAs (Algebra.Etale (Localization.Away f) (Localization.Away f)))
    (fun j => inferInstanceAs (Algebra.Etale (Localization.Away f) (B j)))

def farDeg (deg : Fin M → ℕ) : Fin (M + 1) → ℕ := Fin.cases 1 deg

def farφ (R' : Type) [CommRing R'] [Algebra (Localization.Away f) R'] (deg : Fin M → ℕ)
    (φ : ∀ i, TensorProduct (Localization.Away f) R' (B i) ≃ₐ[R'] (Fin (deg i) → R')) :
    ∀ i, TensorProduct (Localization.Away f) R' (farB f B i) ≃ₐ[R'] (Fin (farDeg deg i) → R') :=
  Fin.cases ((Algebra.TensorProduct.rid (Localization.Away f) R' R').trans (AlgEquiv.funUnique R' (Fin 1) R').symm)
    (fun j => φ j)

def farZ (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ pullback (toBase N₀ q) (specMap (R q) (Localization.Away f))) :
    ∀ i, Spec (CommRingCat.of (farB f B i)) ⟶ pullback (toBase N₀ q) (specMap (R q) (Localization.Away f)) :=
  Fin.cases (sectionBaseChange (Localization.Away f) 𝔓.εzero).1 (fun j => z j ≫ wL 𝔓 f)

theorem farZ_isClosedImmersion (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ pullback (toBase N₀ q) (specMap (R q) (Localization.Away f)))
    [∀ i, IsClosedImmersion (z i)] : ∀ i, IsClosedImmersion (farZ 𝔓 f B z i) :=
  Fin.cases (isClosedImmersion_εzero 𝔓 f) (fun j => inferInstanceAs (IsClosedImmersion (z j ≫ wL 𝔓 f)))

@[scoped simp] theorem farB_zero : farB f B 0 = Localization.Away f := rfl
@[scoped simp] theorem farB_succ (j : Fin M) : farB f B j.succ = B j := rfl
@[scoped simp] theorem farDeg_zero (deg : Fin M → ℕ) : farDeg deg 0 = 1 := rfl
@[scoped simp] theorem farDeg_succ (deg : Fin M → ℕ) (j : Fin M) : farDeg deg j.succ = deg j := rfl
@[scoped simp] theorem farZ_zero (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ pullback (toBase N₀ q) (specMap (R q) (Localization.Away f))) :
    farZ 𝔓 f B z 0 = (sectionBaseChange (Localization.Away f) 𝔓.εzero).1 := rfl
@[scoped simp] theorem farZ_succ (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ pullback (toBase N₀ q) (specMap (R q) (Localization.Away f)))
    (j : Fin M) : farZ 𝔓 f B z j.succ = z j ≫ wL 𝔓 f := rfl

end Far

end TwoSidedAux
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_twoSidedPool_of_oneSided.ModularCurve.DRModelPackageLevel.TwoSidedAux"

end ModularCurve.DRModelPackageLevel
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_twoSidedPool_of_oneSided.ModularCurve.DRModelPackageLevel.TwoSidedAux P2MW.S_ModularCurve_DRModelPackageLevel_exists_twoSidedPool_of_oneSided.ModularCurve P2MW.S_ModularCurve_DRModelPackageLevel_exists_twoSidedPool_of_oneSided.ModularCurve.DRModelPackageLevel"
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_twoSidedPool_of_oneSided.ModularCurve.DRModelPackageLevel.TwoSidedAux P2MW.S_ModularCurve_DRModelPackageLevel_exists_twoSidedPool_of_oneSided.ModularCurve"

open _root_.ModularCurve.DRModelPackageLevel _root_.P2MW.S_ModularCurve_DRModelPackageLevel_exists_twoSidedPool_of_oneSided.ModularCurve.DRModelPackageLevel ModularCurve.DRModelPackageLevel.TwoSidedAux in

theorem solution (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (A₀ B₀ n₀ : ℕ) (f : R q)
    (hfar : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f))),
      ¬ Smooth (pullback.snd (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s) →
      (∀ y : ↥(pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s),
        y ∈ connectedComponentIn
            (((pullback.fst (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s ≫ pullback.fst (toBase N₀ q) (specMap (R q) (Localization.Away f))) ⁻¹ᵁ 𝔓.smoothLocus :
                (pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s))
            (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔓.εinf) s).1).base (IsLocalRing.closedPoint k)) →
        (pullback.map (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s
            (curveChange 𝔓.w.hom 𝔓.w_over (specMap (R q) (Localization.Away f))) (𝟙 _) (𝟙 _)
            ((Category.comp_id _).trans (curveChange_snd _ _ _).symm)
            ((Category.comp_id _).trans (Category.id_comp _).symm)).base y ∈
          (((pullback.fst (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s ≫ pullback.fst (toBase N₀ q) (specMap (R q) (Localization.Away f))) ⁻¹ᵁ 𝔓.smoothLocus :
                (pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s)) \
          connectedComponentIn
            (((pullback.fst (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s ≫ pullback.fst (toBase N₀ q) (specMap (R q) (Localization.Away f))) ⁻¹ᵁ 𝔓.smoothLocus :
                (pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s))
            (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔓.εinf) s).1).base (IsLocalRing.closedPoint k))) ∧
      ((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔓.εzero) s).1).base (IsLocalRing.closedPoint k) ∈
          (((pullback.fst (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s ≫ pullback.fst (toBase N₀ q) (specMap (R q) (Localization.Away f))) ⁻¹ᵁ 𝔓.smoothLocus :
                (pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s)) \
          connectedComponentIn
            (((pullback.fst (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s ≫ pullback.fst (toBase N₀ q) (specMap (R q) (Localization.Away f))) ⁻¹ᵁ 𝔓.smoothLocus :
                (pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s))
            (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔓.εinf) s).1).base (IsLocalRing.closedPoint k)))
    (b M : ℕ) (hM : A₀ * b ^ n₀ + B₀ < M)
    (R' : Type) [CommRing R'] [Algebra (R q) R'] [Algebra (Localization.Away f) R'] [IsScalarTower (R q) (Localization.Away f) R']
    [Module.Finite (Localization.Away f) R'] [Algebra.Etale (Localization.Away f) R'] [Module.FaithfullyFlat (Localization.Away f) R']
    (B : Fin M → Type) [∀ i, CommRing (B i)] [∀ i, Algebra (Localization.Away f) (B i)]
    [∀ i, Module.Finite (Localization.Away f) (B i)] [∀ i, Algebra.Etale (Localization.Away f) (B i)]
    (deg : Fin M → ℕ) (hdeg : ∀ i, 1 ≤ deg i) (hdegb : ∀ i, deg i ≤ b)
    (φ : ∀ i, TensorProduct (Localization.Away f) R' (B i) ≃ₐ[R'] (Fin (deg i) → R'))
    (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ pullback (toBase N₀ q) (specMap (R q) (Localization.Away f)))
    [∀ i, IsClosedImmersion (z i)]
    (hz₁ : ∀ i, z i ≫ baseChange (R q) (toBase N₀ q) (Localization.Away f) = specMap (Localization.Away f) (B i))
    (hz₂ : ∀ i, Set.range (z i).base ⊆
      ((pullback.fst (toBase N₀ q) (specMap (R q) (Localization.Away f)) ⁻¹ᵁ 𝔓.smoothLocus : (pullback (toBase N₀ q) (specMap (R q) (Localization.Away f))).Opens) :
        Set ↥(pullback (toBase N₀ q) (specMap (R q) (Localization.Away f)))))
    (hz₃ : Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base))
    (hz₄ : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
      (i : Fin M),
      (pullback.fst (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s).base ⁻¹' Set.range (z i).base ⊆
        connectedComponentIn
          (((pullback.fst (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s ≫ pullback.fst (toBase N₀ q) (specMap (R q) (Localization.Away f))) ⁻¹ᵁ 𝔓.smoothLocus :
              (pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s))
          (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔓.εinf) s).1).base (IsLocalRing.closedPoint k)))
    (hzinf : ∀ i, Disjoint (Set.range (z i).base) (Set.range (sectionBaseChange (Localization.Away f) 𝔓.εinf).1.base))
    (hzzero : ∀ i, Disjoint (Set.range (z i).base) (Set.range (sectionBaseChange (Localization.Away f) 𝔓.εzero).1.base))
    (hzw : ∀ i j, Disjoint (Set.range (z i).base)
      (Set.range (z j ≫ curveChange 𝔓.w.hom 𝔓.w_over (specMap (R q) (Localization.Away f))).base)) :
    ∃ (b M M' : ℕ)
      (_ : A₀ * b ^ n₀ + B₀ < M) (_ : A₀ * b ^ n₀ + B₀ < M')
      (R' : Type) (_ : CommRing R') (_ : Algebra (R q) R')
      (_ : Algebra (Localization.Away f) R') (_ : IsScalarTower (R q) (Localization.Away f) R')
      (_ : Module.Finite (Localization.Away f) R') (_ : Algebra.Etale (Localization.Away f) R')
      (_ : Module.FaithfullyFlat (Localization.Away f) R')
      (B : Fin M → Type) (_ : ∀ i, CommRing (B i)) (_ : ∀ i, Algebra (Localization.Away f) (B i))
      (_ : ∀ i, Module.Finite (Localization.Away f) (B i)) (_ : ∀ i, Algebra.Etale (Localization.Away f) (B i))
      (deg : Fin M → ℕ) (_ : ∀ i, 1 ≤ deg i) (_ : ∀ i, deg i ≤ b)
      (φ : ∀ i, TensorProduct (Localization.Away f) R' (B i) ≃ₐ[R'] (Fin (deg i) → R'))
      (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ pullback (toBase N₀ q) (specMap (R q) (Localization.Away f)))
      (_ : ∀ i, IsClosedImmersion (z i))
      (B' : Fin M' → Type) (_ : ∀ i, CommRing (B' i)) (_ : ∀ i, Algebra (Localization.Away f) (B' i))
      (_ : ∀ i, Module.Finite (Localization.Away f) (B' i)) (_ : ∀ i, Algebra.Etale (Localization.Away f) (B' i))
      (deg' : Fin M' → ℕ) (_ : ∀ i, 1 ≤ deg' i) (_ : ∀ i, deg' i ≤ b)
      (φ' : ∀ i, TensorProduct (Localization.Away f) R' (B' i) ≃ₐ[R'] (Fin (deg' i) → R'))
      (z' : ∀ i, Spec (CommRingCat.of (B' i)) ⟶ pullback (toBase N₀ q) (specMap (R q) (Localization.Away f)))
      (_ : ∀ i, IsClosedImmersion (z' i)),

      (∀ i, z i ≫ baseChange (R q) (toBase N₀ q) (Localization.Away f) = specMap (Localization.Away f) (B i)) ∧
      (∀ i, Set.range (z i).base ⊆
        ((pullback.fst (toBase N₀ q) (specMap (R q) (Localization.Away f)) ⁻¹ᵁ 𝔓.smoothLocus : (pullback (toBase N₀ q) (specMap (R q) (Localization.Away f))).Opens) :
          Set ↥(pullback (toBase N₀ q) (specMap (R q) (Localization.Away f))))) ∧
      (Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base)) ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
        (i : Fin M),
        (pullback.fst (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s).base ⁻¹' Set.range (z i).base ⊆
          connectedComponentIn
            (((pullback.fst (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s ≫ pullback.fst (toBase N₀ q) (specMap (R q) (Localization.Away f))) ⁻¹ᵁ 𝔓.smoothLocus :
                (pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s))
            (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔓.εinf) s).1).base (IsLocalRing.closedPoint k))) ∧

      (∃ j, deg' j ≤ 1) ∧
      (∀ i, z' i ≫ baseChange (R q) (toBase N₀ q) (Localization.Away f) = specMap (Localization.Away f) (B' i)) ∧
      (∀ i, Set.range (z' i).base ⊆
        ((pullback.fst (toBase N₀ q) (specMap (R q) (Localization.Away f)) ⁻¹ᵁ 𝔓.smoothLocus : (pullback (toBase N₀ q) (specMap (R q) (Localization.Away f))).Opens) :
          Set ↥(pullback (toBase N₀ q) (specMap (R q) (Localization.Away f))))) ∧
      (Pairwise fun i j => Disjoint (Set.range (z' i).base) (Set.range (z' j).base)) ∧
      (∀ i j, Disjoint (Set.range (z i).base) (Set.range (z' j).base)) ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
        (i : Fin M'), ¬ Smooth (pullback.snd (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s) →
        (pullback.fst (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s).base ⁻¹' Set.range (z' i).base ⊆
          (((pullback.fst (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s ≫ pullback.fst (toBase N₀ q) (specMap (R q) (Localization.Away f))) ⁻¹ᵁ 𝔓.smoothLocus :
                (pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s)) \
          connectedComponentIn
            (((pullback.fst (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s ≫ pullback.fst (toBase N₀ q) (specMap (R q) (Localization.Away f))) ⁻¹ᵁ 𝔓.smoothLocus :
                (pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s))
            (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔓.εinf) s).1).base (IsLocalRing.closedPoint k))) := by
  have hM0 : 0 < M := lt_of_le_of_lt (Nat.zero_le _) hM
  have h1b : 1 ≤ b := (hdeg ⟨0, hM0⟩).trans (hdegb ⟨0, hM0⟩)
  refine ⟨b, M, M + 1, hM, Nat.lt_succ_of_lt hM, R', inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, B, inferInstance, inferInstance, inferInstance, inferInstance,
    deg, hdeg, hdegb, φ, z, inferInstance, farB f B, inferInstance, inferInstance, farFinite f B, farEtale f B, farDeg deg,
    Fin.cases le_rfl hdeg, Fin.cases h1b hdegb, farφ f B R' deg φ, farZ 𝔓 f B z, farZ_isClosedImmersion 𝔓 f B z,
    hz₁, hz₂, hz₃, hz₄, ⟨0, le_rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  ·
    refine Fin.cases ?_ (fun j => ?_)
    · show (sectionBaseChange (Localization.Away f) 𝔓.εzero).1 ≫ _ = Spec.map (CommRingCat.ofHom (RingHom.id _))
      rw [(sectionBaseChange (Localization.Away f) 𝔓.εzero).2, CommRingCat.ofHom_id, Spec.map_id]
    · show (z j ≫ wL 𝔓 f) ≫ _ = _
      rw [Category.assoc, wL_snd]
      exact hz₁ j
  ·
    refine Fin.cases (range_εzero_subset 𝔓 f) (fun j => ?_)
    show Set.range (z j ≫ wL 𝔓 f).base ⊆ _
    rw [range_comp_wL]
    rintro _ ⟨x, hx, rfl⟩
    exact wL_base_mem_preimage_smoothLocus 𝔓 f (hz₂ j hx)
  ·
    intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ j =>
        show Disjoint (Set.range (sectionBaseChange (Localization.Away f) 𝔓.εzero).1.base) (Set.range (z j ≫ wL 𝔓 f).base)
        rw [range_εzero_eq, range_comp_wL]
        exact (Set.disjoint_image_iff (wL_base_injective 𝔓 f)).2 (hzinf j).symm
    | succ i =>
      induction j using Fin.cases with
      | zero =>
        show Disjoint (Set.range (z i ≫ wL 𝔓 f).base) (Set.range (sectionBaseChange (Localization.Away f) 𝔓.εzero).1.base)
        rw [range_εzero_eq, range_comp_wL]
        exact (Set.disjoint_image_iff (wL_base_injective 𝔓 f)).2 (hzinf i)
      | succ j =>
        show Disjoint (Set.range (z i ≫ wL 𝔓 f).base) (Set.range (z j ≫ wL 𝔓 f).base)
        rw [range_comp_wL, range_comp_wL]
        exact (Set.disjoint_image_iff (wL_base_injective 𝔓 f)).2 (hz₃ fun h => hij (congrArg Fin.succ h))
  ·
    intro i j
    induction j using Fin.cases with
    | zero => exact hzzero i
    | succ j => exact hzw i j
  ·
    intro k _ _ s i hns
    induction i using Fin.cases with
    | zero =>
      intro y hy
      rw [eq_sectionFibrePoint_of_mem f s (sectionBaseChange (Localization.Away f) 𝔓.εzero) y hy]
      exact (hfar k s hns).2
    | succ j =>
      intro y hy
      change (pullback.fst (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s).base y ∈
        Set.range (z j ≫ wL 𝔓 f).base at hy
      rw [range_comp_wL] at hy
      obtain ⟨x, hx, hxy⟩ := hy
      have hy₀ : (pullback.fst (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s).base ((wLs 𝔓 f s).base y) ∈
          Set.range (z j).base := by
        rw [wLs_fst_base, ← hxy, wL_base_wL_base]
        exact hx
      have key := (hfar k s hns).1 ((wLs 𝔓 f s).base y) (hz₄ k s j hy₀)
      rwa [wLs_base_wLs_base] at key

end
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_twoSidedPool_of_oneSided.ModularCurve.DRModelPackageLevel.TwoSidedAux P2MW.S_ModularCurve_DRModelPackageLevel_exists_twoSidedPool_of_oneSided.ModularCurve P2MW.S_ModularCurve_DRModelPackageLevel_exists_twoSidedPool_of_oneSided.ModularCurve.DRModelPackageLevel"

end S_ModularCurve_DRModelPackageLevel_exists_twoSidedPool_of_oneSided
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_exists_twoSidedPool_of_oneSided (solution)
