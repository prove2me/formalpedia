-- Prove2me | solution 1 for ModularCurve.DRLevel.pointEquivPlace_comp_inv_of_fst_eq_frobenius_comp_eq_arithFrobC_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/0783f94c-c8da-52a6-befb-382396fccb33

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Theorems.Thm_ModularCurve_DRLevel_fromSpecStalk_comp_eq_of_chartPin
import Theorems.Thm_AlgebraicCurve_CurveModel_pointEquivPlace_comp_eq_congrRingEquiv_of_fromSpecStalk_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRLevel_pointEquivPlace_comp_inv_of_fst_eq_frobenius_comp_eq_arithFrobC_smul
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve P2MW.S_ModularCurve_DRLevel_pointEquivPlace_comp_inv_of_fst_eq_frobenius_comp_eq_arithFrobC_smul.AlgebraicCurve NeronModelInfra"
p2m_open "ModularCurve P2MW.S_ModularCurve_DRLevel_pointEquivPlace_comp_inv_of_fst_eq_frobenius_comp_eq_arithFrobC_smul.ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel P2MW.S_ModularCurve_DRLevel_pointEquivPlace_comp_inv_of_fst_eq_frobenius_comp_eq_arithFrobC_smul.ModularCurve.DRLevel"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "baseToFunctionField CurveModel CurveModel.pointEquivPlace_apply Place Place.ext SemilinearAut SemilinearAut.toRingAut SemilinearAut.baseAut SemilinearAut.commutes SemilinearAut.smul_def SemilinearAut.smul_toValuationSubring Place.congrRingEquiv Place.congrRingEquiv_toValuationSubring CurveModel.pointEquivPlace_comp_eq_congrRingEquiv_of_fromSpecStalk_comp_eq"
namespace CurveModel
p2m_export "AlgebraicCurve.CurveModel" "pointEquivPlace pointEquivPlace_apply isProper placeOfPoint toBase C range_stalk_eq ffEquiv finset_subset_affineOpen ffEquiv_algebraMap placeOfPoint_bijective isIntegral smooth pointEquivPlace_comp_eq_congrRingEquiv_of_fromSpecStalk_comp_eq"
namespace TwistPlaceAux
p2m_open "AlgebraicCurve.CurveModel AlgebraicCurve"

universe u v

section BaseToFF

variable {K : Type u} [Field K] {C : Scheme.{u}} [IsIntegral C]

theorem baseToFunctionField_comp_SpecMap (c : C ⟶ Spec (CommRingCat.of K)) (σ : K →+* K) (a : K) :
    baseToFunctionField (c ≫ Spec.map (CommRingCat.ofHom σ)) a = baseToFunctionField c (σ a) := by
  simp only [baseToFunctionField, RingHom.coe_comp, Function.comp_apply, Scheme.Hom.comp_appTop,
    CommRingCat.hom_comp]
  congr 1
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom σ)
  have h' := congrArg (fun φ => φ.hom a) h
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at h'
  exact congrArg _ h'.symm

end BaseToFF

section Twist

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]

open scoped Pointwise

scoped instance isIso_SpecMap_ofHom_ringEquiv (σ : K ≃+* K) :
    IsIso (Spec.map (CommRingCat.ofHom (σ : K →+* K))) :=
  show IsIso (Spec.map σ.toCommRingCatIso.hom) from inferInstance

@[reducible] noncomputable def twist (M : CurveModel K L) (g : SemilinearAut K L) : CurveModel K L where
  C := M.C
  toBase := M.toBase ≫ Spec.map (CommRingCat.ofHom (SemilinearAut.baseAut g : K →+* K))
  isIntegral := M.isIntegral
  isProper := inferInstance
  smooth := show SmoothOfRelativeDimension (1 + 0) _ from inferInstance
  ffEquiv := (SemilinearAut.toRingAut g).trans M.ffEquiv
  ffEquiv_algebraMap a := by
    rw [baseToFunctionField_comp_SpecMap, RingEquiv.trans_apply, ← M.ffEquiv_algebraMap]
    congr 1
    exact SemilinearAut.commutes g a
  placeOfPoint x := g⁻¹ • M.placeOfPoint x
  placeOfPoint_bijective := (MulAction.bijective g⁻¹).comp M.placeOfPoint_bijective
  range_stalk_eq x := by
    ext z
    change (∃ s, ((SemilinearAut.toRingAut g).trans M.ffEquiv).symm (algebraMap _ _ s) = z) ↔
      z ∈ ((g⁻¹ • M.placeOfPoint x).toValuationSubring).toSubring
    rw [ValuationSubring.mem_toSubring, SemilinearAut.smul_toValuationSubring,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, inv_inv, ← ValuationSubring.mem_toSubring,
      ← M.range_stalk_eq x, RingHom.mem_range]
    constructor
    · rintro ⟨s, rfl⟩
      refine ⟨s, ?_⟩
      simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
        RingEquiv.symm_trans_apply, SemilinearAut.smul_def, RingEquiv.apply_symm_apply]
    · rintro ⟨s, hs⟩
      refine ⟨s, ?_⟩
      simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply] at hs
      rw [RingEquiv.symm_trans_apply, hs, SemilinearAut.smul_def, RingEquiv.symm_apply_apply]
  finset_subset_affineOpen := M.finset_subset_affineOpen

variable (M : CurveModel K L) (g : SemilinearAut K L)

theorem twist_C : (twist M g).C = M.C := rfl

theorem twist_toBase :
    (twist M g).toBase = M.toBase ≫ Spec.map (CommRingCat.ofHom (SemilinearAut.baseAut g : K →+* K)) := rfl

theorem twist_ffEquiv : (twist M g).ffEquiv = (SemilinearAut.toRingAut g).trans M.ffEquiv := rfl

theorem twist_ffEquiv_symm_apply (t : M.C.functionField) :
    (twist M g).ffEquiv.symm t = g⁻¹ • M.ffEquiv.symm t := rfl

theorem twist_placeOfPoint (x : closedPoints M.C) :
    (twist M g).placeOfPoint x = g⁻¹ • M.placeOfPoint x := rfl

theorem twist_pointEquivPlace [IsAlgClosed K]
    (p : {p : Spec (CommRingCat.of K) ⟶ (twist M g).C // p ≫ (twist M g).toBase = 𝟙 _}) :
    (twist M g).pointEquivPlace p =
      g⁻¹ • M.placeOfPoint ⟨p.1.base (IsLocalRing.closedPoint K), (pointEquivClosedPoint (twist M g).toBase p).2⟩ := rfl

end Twist

end AlgebraicCurve.CurveModel.TwistPlaceAux
p2m_reactivate "P2MW.S_ModularCurve_DRLevel_pointEquivPlace_comp_inv_of_fst_eq_frobenius_comp_eq_arithFrobC_smul.AlgebraicCurve P2MW.S_ModularCurve_DRLevel_pointEquivPlace_comp_inv_of_fst_eq_frobenius_comp_eq_arithFrobC_smul.AlgebraicCurve.CurveModel P2MW.S_ModularCurve_DRLevel_pointEquivPlace_comp_inv_of_fst_eq_frobenius_comp_eq_arithFrobC_smul.AlgebraicCurve.CurveModel.TwistPlaceAux"
p2m_reactivate "P2MW.S_ModularCurve_DRLevel_pointEquivPlace_comp_inv_of_fst_eq_frobenius_comp_eq_arithFrobC_smul.AlgebraicCurve P2MW.S_ModularCurve_DRLevel_pointEquivPlace_comp_inv_of_fst_eq_frobenius_comp_eq_arithFrobC_smul.AlgebraicCurve.CurveModel"
p2m_reactivate "P2MW.S_ModularCurve_DRLevel_pointEquivPlace_comp_inv_of_fst_eq_frobenius_comp_eq_arithFrobC_smul.AlgebraicCurve"

namespace ModularCurve
p2m_export "ModularCurve" "DRLevel.R DRLevel.toBase0 DRLevel.fibre0 IgusaScheme.chartAlgFin IgusaScheme.jChartFin IgusaScheme IgusaScheme.ιFin qExpand jq modularFunctionFieldFull jGeomGen jNGeomGen modularFunctionFieldC arithFrobC arithFrobC_smul_jq arithFrobC_smul_jqN DRLevel.fromSpecStalk_comp_eq_of_chartPin"
namespace DRLevel
p2m_export "ModularCurve.DRLevel" "R X toBase toBase0 fibre fibre0 fromSpecStalk_comp_eq_of_chartPin"
namespace TwistPlaceAux
p2m_open "ModularCurve.DRLevel ModularCurve"

open AlgebraicCurve.CurveModel.TwistPlaceAux

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime]

theorem frobenius_comp_toκ (κ : Type) [Field κ] [CharP κ q] (toκ : DRLevel.R q →+* κ) :
    (frobenius κ q).comp toκ = toκ := by
  ext x
  have hd : (((x : ℚ).den : ℕ) : κ) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff κ q]
    exact fun h => (Fact.out : q.Prime).ne_one (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm x.2) h)
  have hxR : x * (((x : ℚ).den : ℕ) : DRLevel.R q) = (((x : ℚ).num : ℤ) : DRLevel.R q) :=
    Subtype.ext (by push_cast; exact Rat.mul_den_eq_num _)
  have h1 : toκ x * (((x : ℚ).den : ℕ) : κ) = (((x : ℚ).num : ℤ) : κ) := by
    have := congrArg toκ hxR
    rwa [map_mul, map_natCast, map_intCast] at this
  rw [RingHom.comp_apply]
  apply mul_right_cancel₀ hd
  rw [← map_natCast (frobenius κ q), ← map_mul, h1, map_intCast, ← h1, map_natCast]

section W

variable (κ : Type) [Field κ] [CharP κ q] (toκ : DRLevel.R q →+* κ)

noncomputable def W : DRLevel.fibre0 (N₀ := N₀) toκ ⟶ DRLevel.fibre0 (N₀ := N₀) toκ :=
  pullback.map (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ)) (DRLevel.toBase0 N₀ q)
    (Spec.map (CommRingCat.ofHom toκ)) (𝟙 _) (Spec.map (CommRingCat.ofHom (frobenius κ q))) (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, frobenius_comp_toκ])

@[reassoc (attr := simp)]
theorem W_fst : W (N₀ := N₀) κ toκ ≫ pullback.fst _ _ = pullback.fst _ _ :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc (attr := simp)]
theorem W_snd : W (N₀ := N₀) κ toκ ≫ pullback.snd _ _ =
    pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (frobenius κ q)) :=
  pullback.lift_snd _ _ _

scoped instance isIso_SpecMap_frobenius [IsAlgClosed κ] : IsIso (Spec.map (CommRingCat.ofHom (frobenius κ q))) := by
  have h : frobenius κ q = ((frobeniusEquiv κ q : κ ≃+* κ) : κ →+* κ) := RingHom.ext fun a => (frobeniusEquiv_apply κ q a).symm
  rw [h]
  infer_instance

scoped instance isIso_W [IsAlgClosed κ] : IsIso (W (N₀ := N₀) κ toκ) := by
  unfold W; infer_instance

end W
p2m_reactivate "P2MW.S_ModularCurve_DRLevel_pointEquivPlace_comp_inv_of_fst_eq_frobenius_comp_eq_arithFrobC_smul.AlgebraicCurve P2MW.S_ModularCurve_DRLevel_pointEquivPlace_comp_inv_of_fst_eq_frobenius_comp_eq_arithFrobC_smul.AlgebraicCurve.CurveModel P2MW.S_ModularCurve_DRLevel_pointEquivPlace_comp_inv_of_fst_eq_frobenius_comp_eq_arithFrobC_smul.AlgebraicCurve.CurveModel.TwistPlaceAux"

theorem germ_read_eq {X Y : Scheme} [IrreducibleSpace X] {f f' : X ⟶ Y} (h : f = f') (V : Y.Opens)
    [Nonempty (Scheme.Opens.toScheme (f ⁻¹ᵁ V))] [Nonempty (Scheme.Opens.toScheme (f' ⁻¹ᵁ V))] (t : Γ(Y, V)) :
    X.germToFunctionField (f ⁻¹ᵁ V) ((f.app V).hom t) = X.germToFunctionField (f' ⁻¹ᵁ V) ((f'.app V).hom t) := by
  subst h; rfl

theorem inv_arithFrobC_smul_jGeomGen (κ : Type) [Field κ] [CharP κ q] [PerfectField κ] (N : ℕ) [NeZero N] :
    (arithFrobC q κ N)⁻¹ • jGeomGen κ N = jGeomGen κ N :=
  inv_smul_eq_iff.mpr (arithFrobC_smul_jq q κ N).symm

theorem inv_arithFrobC_smul_jNGeomGen (κ : Type) [Field κ] [CharP κ q] [PerfectField κ] (N : ℕ) [NeZero N] :
    (arithFrobC q κ N)⁻¹ • jNGeomGen κ N = jNGeomGen κ N :=
  inv_smul_eq_iff.mpr (arithFrobC_smul_jqN q κ N).symm

theorem congrRingEquiv_refl {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    Place.congrRingEquiv (e := RingEquiv.refl F) (he := fun _ => rfl) v = v := by
  refine Place.ext ?_
  rw [Place.congrRingEquiv_toValuationSubring]
  ext f
  rw [ValuationSubring.mem_comap]
  rfl

end ModularCurve.DRLevel.TwistPlaceAux
p2m_reactivate "P2MW.S_ModularCurve_DRLevel_pointEquivPlace_comp_inv_of_fst_eq_frobenius_comp_eq_arithFrobC_smul.AlgebraicCurve P2MW.S_ModularCurve_DRLevel_pointEquivPlace_comp_inv_of_fst_eq_frobenius_comp_eq_arithFrobC_smul.AlgebraicCurve.CurveModel P2MW.S_ModularCurve_DRLevel_pointEquivPlace_comp_inv_of_fst_eq_frobenius_comp_eq_arithFrobC_smul.AlgebraicCurve.CurveModel.TwistPlaceAux P2MW.S_ModularCurve_DRLevel_pointEquivPlace_comp_inv_of_fst_eq_frobenius_comp_eq_arithFrobC_smul.ModularCurve P2MW.S_ModularCurve_DRLevel_pointEquivPlace_comp_inv_of_fst_eq_frobenius_comp_eq_arithFrobC_smul.ModularCurve.DRLevel P2MW.S_ModularCurve_DRLevel_pointEquivPlace_comp_inv_of_fst_eq_frobenius_comp_eq_arithFrobC_smul.ModularCurve.DRLevel.TwistPlaceAux"
p2m_reactivate "P2MW.S_ModularCurve_DRLevel_pointEquivPlace_comp_inv_of_fst_eq_frobenius_comp_eq_arithFrobC_smul.AlgebraicCurve P2MW.S_ModularCurve_DRLevel_pointEquivPlace_comp_inv_of_fst_eq_frobenius_comp_eq_arithFrobC_smul.AlgebraicCurve.CurveModel P2MW.S_ModularCurve_DRLevel_pointEquivPlace_comp_inv_of_fst_eq_frobenius_comp_eq_arithFrobC_smul.AlgebraicCurve.CurveModel.TwistPlaceAux P2MW.S_ModularCurve_DRLevel_pointEquivPlace_comp_inv_of_fst_eq_frobenius_comp_eq_arithFrobC_smul.ModularCurve P2MW.S_ModularCurve_DRLevel_pointEquivPlace_comp_inv_of_fst_eq_frobenius_comp_eq_arithFrobC_smul.ModularCurve.DRLevel"
p2m_reactivate "P2MW.S_ModularCurve_DRLevel_pointEquivPlace_comp_inv_of_fst_eq_frobenius_comp_eq_arithFrobC_smul.AlgebraicCurve P2MW.S_ModularCurve_DRLevel_pointEquivPlace_comp_inv_of_fst_eq_frobenius_comp_eq_arithFrobC_smul.AlgebraicCurve.CurveModel P2MW.S_ModularCurve_DRLevel_pointEquivPlace_comp_inv_of_fst_eq_frobenius_comp_eq_arithFrobC_smul.AlgebraicCurve.CurveModel.TwistPlaceAux P2MW.S_ModularCurve_DRLevel_pointEquivPlace_comp_inv_of_fst_eq_frobenius_comp_eq_arithFrobC_smul.ModularCurve"

open ModularCurve.DRLevel.TwistPlaceAux AlgebraicCurve.CurveModel.TwistPlaceAux

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)

    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : DRLevel.R q →+* κ)

    (M : CurveModel κ ↥(modularFunctionFieldC κ N₀)) (e : M.C ⟶ DRLevel.fibre0 (N₀ := N₀) toκ) [IsIso e]
    (heM : e ≫ pullback.snd _ _ = M.toBase)
    [hMne : Nonempty (Scheme.Opens.toScheme ((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) ⁻¹ᵁ
      ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤)))]
    (hMpin : ∀ b : ↥(IgusaScheme.chartAlgFin N₀ q),
        let readb : ↥(modularFunctionFieldC κ N₀) :=
          M.ffEquiv.symm
            (M.C.germToFunctionField
              ((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) ⁻¹ᵁ ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤))
              (((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))).app ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤)).hom
                (((IgusaScheme.ιFin N₀ q).appIso ⊤).inv
                  ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin N₀ q))).inv b))))
        ((b = IgusaScheme.jChartFin N₀ q → readb = jGeomGen κ N₀) ∧
          (((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ) = qExpand ℚ N₀ jq → readb = jNGeomGen κ N₀)))

    (x : Spec (CommRingCat.of κ) ⟶ DRLevel.fibre0 (N₀ := N₀) toκ) (hx : x ≫ pullback.snd _ _ = 𝟙 _)
    (y : Spec (CommRingCat.of κ) ⟶ DRLevel.fibre0 (N₀ := N₀) toκ) (hy : y ≫ pullback.snd _ _ = 𝟙 _)
    (hyx : y ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (frobenius κ q)) ≫ x ≫ pullback.fst _ _) :
    M.pointEquivPlace ⟨y ≫ inv e, by rw [Category.assoc, ← heM, IsIso.inv_hom_id_assoc, hy]⟩ =
      arithFrobC q κ N₀ • M.pointEquivPlace ⟨x ≫ inv e, by rw [Category.assoc, ← heM, IsIso.inv_hom_id_assoc, hx]⟩ := by

  have hσ : (SemilinearAut.baseAut (arithFrobC q κ N₀) : κ →+* κ) = frobenius κ q := RingHom.ext fun a => rfl

  have hMσ : (twist M (arithFrobC q κ N₀)).toBase = M.toBase ≫ Spec.map (CommRingCat.ofHom (frobenius κ q)) := by
    rw [twist_toBase, hσ]

  have hfst : (e ≫ W (N₀ := N₀) κ toκ) ≫ pullback.fst _ _ = e ≫ pullback.fst _ _ := by
    rw [Category.assoc, W_fst]
  have heM' : (e ≫ W (N₀ := N₀) κ toκ) ≫ pullback.snd _ _ = (twist M (arithFrobC q κ N₀)).toBase := by
    rw [hMσ, Category.assoc, W_snd, ← Category.assoc, heM]
  haveI hMne' : Nonempty (Scheme.Opens.toScheme (((e ≫ W (N₀ := N₀) κ toκ) ≫ pullback.fst (DRLevel.toBase0 N₀ q)
      (Spec.map (CommRingCat.ofHom toκ))) ⁻¹ᵁ ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤))) := by
    rw [hfst]; exact hMne

  have hgen := ModularCurve.DRLevel.fromSpecStalk_comp_eq_of_chartPin N₀ q hqN κ toκ
    (twist M (arithFrobC q κ N₀)) (e ≫ W (N₀ := N₀) κ toκ) heM' (hMne := hMne') ?pin M e heM (hMne' := hMne) hMpin
  case pin =>
    intro b
    have key := germ_read_eq (X := M.C) hfst ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤)
      (((IgusaScheme.ιFin N₀ q).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin N₀ q))).inv b))
    obtain ⟨h1, h2⟩ := hMpin b
    refine ⟨fun hb => ?_, fun hb => ?_⟩
    · show (twist M (arithFrobC q κ N₀)).ffEquiv.symm _ = _
      rw [twist_ffEquiv_symm_apply, key, h1 hb]
      exact inv_arithFrobC_smul_jGeomGen κ N₀
    · show (twist M (arithFrobC q κ N₀)).ffEquiv.symm _ = _
      rw [twist_ffEquiv_symm_apply, key, h2 hb]
      exact inv_arithFrobC_smul_jNGeomGen κ N₀

  have hθ : ((e ≫ W (N₀ := N₀) κ toκ) ≫ inv e) ≫ M.toBase = (twist M (arithFrobC q κ N₀)).toBase := by
    rw [← heM', Category.assoc, ← heM, IsIso.inv_hom_id_assoc]
  have hid : (RingEquiv.refl ↥(modularFunctionFieldC κ N₀)).symm.toRingHom.comp M.ffEquiv.symm.toRingHom =
      M.ffEquiv.symm.toRingHom := RingHom.ext fun _ => rfl
  have hθgen : (twist M (arithFrobC q κ N₀)).C.fromSpecStalk (genericPoint (twist M (arithFrobC q κ N₀)).C) ≫
      (e ≫ W (N₀ := N₀) κ toκ) ≫ inv e =
      Spec.map (CommRingCat.ofHom ((twist M (arithFrobC q κ N₀)).ffEquiv.toRingHom.comp
        ((RingEquiv.refl ↥(modularFunctionFieldC κ N₀)).symm.toRingHom.comp M.ffEquiv.symm.toRingHom))) ≫
        M.C.fromSpecStalk (genericPoint M.C) := by
    rw [hid]; exact hgen

  have hz : (x ≫ inv (W (N₀ := N₀) κ toκ) ≫ inv e) ≫ (twist M (arithFrobC q κ N₀)).toBase = 𝟙 _ := by
    rw [hMσ, ← heM]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    rw [← W_snd, IsIso.inv_hom_id_assoc, hx]
  have h5 := AlgebraicCurve.CurveModel.pointEquivPlace_comp_eq_congrRingEquiv_of_fromSpecStalk_comp_eq
    (twist M (arithFrobC q κ N₀)) M (RingEquiv.refl _) (fun _ => rfl) ((e ≫ W (N₀ := N₀) κ toκ) ≫ inv e) hθ hθgen
    ⟨x ≫ inv (W (N₀ := N₀) κ toκ) ≫ inv e, hz⟩
  rw [congrRingEquiv_refl, twist_pointEquivPlace] at h5

  have hzθ : (x ≫ inv (W (N₀ := N₀) κ toκ) ≫ inv e) ≫ (e ≫ W (N₀ := N₀) κ toκ) ≫ inv e = x ≫ inv e := by
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
  have hL : M.pointEquivPlace ⟨x ≫ inv e, by rw [Category.assoc, ← heM, IsIso.inv_hom_id_assoc, hx]⟩ =
      M.pointEquivPlace ⟨(x ≫ inv (W (N₀ := N₀) κ toκ) ≫ inv e) ≫ (e ≫ W (N₀ := N₀) κ toκ) ≫ inv e,
        by rw [Category.assoc, hθ, hz]⟩ := by
    exact congrArg M.pointEquivPlace (Subtype.ext hzθ.symm)

  have hyW : y ≫ W (N₀ := N₀) κ toκ = Spec.map (CommRingCat.ofHom (frobenius κ q)) ≫ x := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, W_fst, hyx]
    · rw [Category.assoc, Category.assoc, W_snd, ← Category.assoc, hy, Category.id_comp, hx, Category.comp_id]
  have hy' : y ≫ inv e = Spec.map (CommRingCat.ofHom (frobenius κ q)) ≫ (x ≫ inv (W (N₀ := N₀) κ toκ) ≫ inv e) := by
    rw [← Category.assoc (Spec.map _), ← hyW]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  have hpt : (y ≫ inv e).base (IsLocalRing.closedPoint κ) =
      (x ≫ inv (W (N₀ := N₀) κ toκ) ≫ inv e).base (IsLocalRing.closedPoint κ) := by
    have hcp : (Spec.map (CommRingCat.ofHom (frobenius κ q))).base (IsLocalRing.closedPoint κ) =
        IsLocalRing.closedPoint κ := Subsingleton.elim _ _
    rw [hy', Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply, hcp]
  have hR : M.pointEquivPlace ⟨y ≫ inv e, by rw [Category.assoc, ← heM, IsIso.inv_hom_id_assoc, hy]⟩ =
      M.placeOfPoint ⟨(x ≫ inv (W (N₀ := N₀) κ toκ) ≫ inv e).base (IsLocalRing.closedPoint κ),
        (pointEquivClosedPoint (twist M (arithFrobC q κ N₀)).toBase ⟨x ≫ inv (W (N₀ := N₀) κ toκ) ≫ inv e, hz⟩).2⟩ := by
    rw [AlgebraicCurve.CurveModel.pointEquivPlace_apply]
    exact congrArg M.placeOfPoint (Subtype.ext hpt)
  rw [hR, hL, h5, smul_inv_smul]

end S_ModularCurve_DRLevel_pointEquivPlace_comp_inv_of_fst_eq_frobenius_comp_eq_arithFrobC_smul
end P2MW
export P2MW.S_ModularCurve_DRLevel_pointEquivPlace_comp_inv_of_fst_eq_frobenius_comp_eq_arithFrobC_smul (solution)
