-- Prove2me | solution 1 for LanglandsTunnell.Converse.chiDetGL_eq_prod_localChar_det_componentAt3_of_isArchCompAt_zero_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/1fe5fe25-8a10-52db-971b-1592a902eb59

import Mathlib
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_CubicInduction_FnTwist3
import Definitions.Def_NumberField_IdeleBox
import Theorems.Thm_NumberField_TateGlobal_apply_eq_one_of_forall_isUnramifiedCharAt_of_continuous
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_chiDetGL_eq_prod_localChar_det_componentAt3_of_isArchCompAt_zero_zero

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField NumberField.TateGlobal LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_chiDetGL_eq_prod_localChar_det_componentAt3_of_isArchCompAt_zero_zero.LanglandsTunnell.Converse LanglandsTunnell.CubicInduction"

noncomputable section

namespace LanglandsTunnell
namespace Converse
p2m_export "LanglandsTunnell.Converse" "IsAdmissibleTwist IsArchCompAt"
namespace ChiDetFactor
p2m_open "LanglandsTunnell.Converse LanglandsTunnell"

open NumberField.AdelicLevel NumberField.AdeleRing

variable (F : Type) [Field F] [NumberField F]

theorem infiniteUnitsComponent_archUnitHom_self (w : InfinitePlace F) (a : (w.Completion)ˣ) :
    infiniteUnitsComponent (𝓞 F) F w (archUnitHom w a) = a := by
  classical
  apply Units.ext
  rw [val_infiniteUnitsComponent]
  show Function.update (1 : InfiniteAdeleRing F) w (a : w.Completion) w = a
  rw [Function.update_self]

theorem infiniteUnitsComponent_archUnitHom_of_ne {w w' : InfinitePlace F} (h : w' ≠ w) (a : (w.Completion)ˣ) :
    infiniteUnitsComponent (𝓞 F) F w' (archUnitHom w a) = 1 := by
  classical
  apply Units.ext
  rw [val_infiniteUnitsComponent]
  show Function.update (1 : InfiniteAdeleRing F) w (a : w.Completion) w' = 1
  rw [Function.update_of_ne h]
  rfl

theorem finiteUnitsComponent_archUnitHom (w : InfinitePlace F) (a : (w.Completion)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    finiteUnitsComponent (𝓞 F) F v (archUnitHom w a) = 1 := by
  apply Units.ext
  rw [val_finiteUnitsComponent]
  rfl

theorem infiniteUnitsComponent_finIncl (y : (FiniteAdeleRing (𝓞 F) F)ˣ) (w : InfinitePlace F) :
    infiniteUnitsComponent (𝓞 F) F w (Units.map (finIncl (𝓞 F) F) y) = 1 := by
  apply Units.ext
  rw [val_infiniteUnitsComponent]
  rfl

theorem finiteUnitsComponent_finIncl_localUnit_self (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    finiteUnitsComponent (𝓞 F) F v (Units.map (finIncl (𝓞 F) F) (localUnit (𝓞 F) F v t)) = t := by
  apply Units.ext
  rw [val_finiteUnitsComponent]
  show ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v = t
  exact localUnit_apply_self (𝓞 F) F v t

theorem finiteUnitsComponent_finIncl_localUnit_of_ne {v v' : HeightOneSpectrum (𝓞 F)} (h : v' ≠ v)
    (t : (v.adicCompletion F)ˣ) :
    finiteUnitsComponent (𝓞 F) F v' (Units.map (finIncl (𝓞 F) F) (localUnit (𝓞 F) F v t)) = 1 := by
  apply Units.ext
  rw [val_finiteUnitsComponent]
  show ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v' = 1
  exact localUnit_apply_of_ne (𝓞 F) F v t h

theorem idele_ext {x y : (AdeleRing (𝓞 F) F)ˣ}
    (hinf : ∀ w, infiniteUnitsComponent (𝓞 F) F w x = infiniteUnitsComponent (𝓞 F) F w y)
    (hfin : ∀ v, finiteUnitsComponent (𝓞 F) F v x = finiteUnitsComponent (𝓞 F) F v y) : x = y := by
  apply Units.ext
  refine Prod.ext (funext fun w => ?_) (FiniteAdeleRing.ext F fun v => ?_)
  · have h := congrArg (fun u : (w.Completion)ˣ => (u : w.Completion)) (hinf w)
    simpa only [val_infiniteUnitsComponent] using h
  · have h := congrArg (fun u : (v.adicCompletion F)ˣ => (u : v.adicCompletion F)) (hfin v)
    simpa only [val_finiteUnitsComponent] using h

theorem valued_det_le_one {v : HeightOneSpectrum (𝓞 F)} (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion F))
    (hk : ∀ i j, Valued.v (k i j) ≤ 1) : Valued.v k.det ≤ 1 := by

  let M : Matrix (Fin 3) (Fin 3) (v.adicCompletionIntegers F) := Matrix.of fun i j =>
    ⟨k i j, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hk i j)⟩
  have hM : k = M.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) := by
    ext i j; rfl
  rw [hM, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (M.det).2

end LanglandsTunnell.Converse.ChiDetFactor

namespace LanglandsTunnell namespace Converse p2m_export "LanglandsTunnell.Converse" "IsAdmissibleTwist IsArchCompAt" namespace ChiDetFactor end LanglandsTunnell.Converse.ChiDetFactor
p2m_open_scoped "LanglandsTunnell LanglandsTunnell.Converse" in
open LanglandsTunnell.Converse.ChiDetFactor NumberField.AdelicLevel NumberField.AdeleRing in

theorem LanglandsTunnell.Converse.ChiDetFactor.main
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχ : IsAdmissibleTwist ℚ χ)
    (hev : ∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ χ w 0 0)
    (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (hT : ∀ v, v ∉ T → IsUnramifiedCharAt χ v)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : ∀ v, v ∉ T → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    chiDetGL 3 (𝓞 ℚ) ℚ χ g =
      ∏ v ∈ T, ((localChar χ v (Matrix.GeneralLinearGroup.det (componentAt3 (𝓞 ℚ) ℚ v g)) : ℂˣ) : ℂ) := by
  classical
  set d : (AdeleRing (𝓞 ℚ) ℚ)ˣ := Matrix.GeneralLinearGroup.det g with hd
  set dv : (v : HeightOneSpectrum (𝓞 ℚ)) → (v.adicCompletion ℚ)ˣ := fun v =>
    Matrix.GeneralLinearGroup.det (componentAt3 (𝓞 ℚ) ℚ v g) with hdv

  have hdvd : ∀ v, finiteUnitsComponent (𝓞 ℚ) ℚ v d = dv v := by
    intro v
    apply Units.ext
    rw [val_finiteUnitsComponent, hdv]
    simp only
    rw [show componentAt3 (𝓞 ℚ) ℚ v = componentAtN (Fin 3) (𝓞 ℚ) ℚ v from rfl, componentAtN,
      Matrix.GeneralLinearGroup.map_det, Units.coe_map]
    rfl

  set dT : (AdeleRing (𝓞 ℚ) ℚ)ˣ := ∏ v ∈ T, Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v (dv v)) with hdT
  set dInf : (AdeleRing (𝓞 ℚ) ℚ)ˣ := ∏ w : InfinitePlace ℚ, archUnitHom w (infiniteUnitsComponent (𝓞 ℚ) ℚ w d)
    with hdInf
  set u : (AdeleRing (𝓞 ℚ) ℚ)ˣ := d * (dInf * dT)⁻¹ with hu
  have hsplit : d = dInf * dT * u := by
    rw [hu, mul_comm d, ← mul_assoc, mul_inv_cancel, one_mul]

  have hcompInf : ∀ w, infiniteUnitsComponent (𝓞 ℚ) ℚ w (dInf * dT) = infiniteUnitsComponent (𝓞 ℚ) ℚ w d := by
    intro w
    rw [map_mul, hdT, hdInf, map_prod, map_prod, Finset.prod_eq_one (fun v _ => infiniteUnitsComponent_finIncl ℚ _ w),
      mul_one, Finset.prod_eq_single w]
    · exact infiniteUnitsComponent_archUnitHom_self ℚ w _
    · intro w' _ hw'
      exact infiniteUnitsComponent_archUnitHom_of_ne ℚ hw'.symm _
    · intro h
      exact absurd (Finset.mem_univ w) h
  have hcompFin : ∀ v, finiteUnitsComponent (𝓞 ℚ) ℚ v (dInf * dT) = if v ∈ T then dv v else 1 := by
    intro v
    rw [map_mul, hdInf, hdT, map_prod, map_prod, Finset.prod_eq_one (fun w _ => finiteUnitsComponent_archUnitHom ℚ w _ v),
      one_mul]
    split_ifs with hv
    · rw [Finset.prod_eq_single v]
      · exact finiteUnitsComponent_finIncl_localUnit_self ℚ v _
      · intro v' _ hv'
        exact finiteUnitsComponent_finIncl_localUnit_of_ne ℚ hv'.symm _
      · intro h
        exact absurd hv h
    · refine Finset.prod_eq_one fun v' hv' => finiteUnitsComponent_finIncl_localUnit_of_ne ℚ ?_ _
      intro h
      rw [h] at hv
      exact hv hv'

  have hu_inf : ∀ w, infiniteUnitsComponent (𝓞 ℚ) ℚ w u = 1 := by
    intro w
    rw [hu, map_mul, map_inv, hcompInf, mul_inv_cancel]
  have hu_fin : ∀ v, finiteUnitsComponent (𝓞 ℚ) ℚ v u = if v ∈ T then 1 else dv v := by
    intro v
    rw [hu, map_mul, map_inv, hcompFin, hdvd]
    split_ifs <;> simp
  have hu1 : (u : AdeleRing (𝓞 ℚ) ℚ).1 = 1 := by
    funext w
    have h := congrArg (fun z : (w.Completion)ˣ => (z : w.Completion)) (hu_inf w)
    simp only [val_infiniteUnitsComponent] at h
    exact h
  have hu2 : ∀ v ∈ T, (u : AdeleRing (𝓞 ℚ) ℚ).2 v = 1 := by
    intro v hv
    have h := congrArg (fun z : (v.adicCompletion ℚ)ˣ => (z : v.adicCompletion ℚ)) (hu_fin v)
    simp only [val_finiteUnitsComponent, if_pos hv, Units.val_one] at h
    exact h
  have hu3 : finitePartUnits (𝓞 ℚ) ℚ u ∈ FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ := by
    rw [FiniteAdeleRing.mem_unitIdeles_iff]
    have hval : ∀ v, ((finitePartUnits (𝓞 ℚ) ℚ u : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v =
        ((finiteUnitsComponent (𝓞 ℚ) ℚ v u : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) := fun v =>
      (FiniteAdeleRing.val_unitsComponent v _).symm
    have hval' : ∀ v, (((finitePartUnits (𝓞 ℚ) ℚ u)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v =
        (((finiteUnitsComponent (𝓞 ℚ) ℚ v u)⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) := fun v => by
      rw [← map_inv, ← map_inv]
      exact (FiniteAdeleRing.val_unitsComponent v _).symm
    have hint : ∀ v, v ∉ T → ((dv v : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ ∧
        (((dv v)⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ := by
      intro v hv
      obtain ⟨h1, h2⟩ := hg v hv
      refine ⟨?_, ?_⟩
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hdv]
        simp only
        rw [Matrix.GeneralLinearGroup.val_det_apply]
        exact valued_det_le_one ℚ _ h1
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hdv]
        simp only
        rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
        exact valued_det_le_one ℚ _ h2
    constructor
    · intro v
      rw [hval v, hu_fin v]
      split_ifs with hv
      · rw [Units.val_one]; exact one_mem _
      · exact (hint v hv).1
    · intro v
      rw [hval' v, hu_fin v]
      split_ifs with hv
      · rw [inv_one, Units.val_one]; exact one_mem _
      · exact (hint v hv).2
  have hχu : χ u = 1 :=
    NumberField.TateGlobal.apply_eq_one_of_forall_isUnramifiedCharAt_of_continuous ℚ χ hχ.2.1 T
      (fun v hv => hT v hv) u hu1 hu2 hu3

  have hχinf : χ dInf = 1 := by
    rw [hdInf, map_prod]
    refine Finset.prod_eq_one fun w _ => ?_
    have h := hev w (NumberField.StandardAddChar.isReal_rat_infinitePlace w) (infiniteUnitsComponent (𝓞 ℚ) ℚ w d)
    rw [mul_zero, Complex.cpow_zero, zpow_zero, mul_one] at h
    exact Units.val_eq_one.1 h

  have hχT : ((χ dT : ℂˣ) : ℂ) = ∏ v ∈ T, ((localChar χ v (dv v) : ℂˣ) : ℂ) := by
    rw [hdT, map_prod, Units.coe_prod]
    rfl
  show ((χ d : ℂˣ) : ℂ) = _
  rw [hsplit, map_mul, map_mul, hχinf, one_mul, hχu, mul_one, hχT]

theorem solution
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχ : IsAdmissibleTwist ℚ χ)
    (hev : ∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ χ w 0 0)
    (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (hT : ∀ v, v ∉ T → IsUnramifiedCharAt χ v)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : ∀ v, v ∉ T → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    chiDetGL 3 (𝓞 ℚ) ℚ χ g =
      ∏ v ∈ T, ((localChar χ v (Matrix.GeneralLinearGroup.det (componentAt3 (𝓞 ℚ) ℚ v g)) : ℂˣ) : ℂ) :=
  LanglandsTunnell.Converse.ChiDetFactor.main χ hχ hev T hT g hg

end
end S_LanglandsTunnell_Converse_chiDetGL_eq_prod_localChar_det_componentAt3_of_isArchCompAt_zero_zero
end P2MW
export P2MW.S_LanglandsTunnell_Converse_chiDetGL_eq_prod_localChar_det_componentAt3_of_isArchCompAt_zero_zero (solution)
