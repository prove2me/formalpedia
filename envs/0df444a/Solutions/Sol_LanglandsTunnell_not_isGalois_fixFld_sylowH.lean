-- Prove2me | solution 1 for LanglandsTunnell.not_isGalois_fixFld_sylowH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/63a9b1ee-9f31-5dec-a812-89efbdb2af9a

import Definitions.Def_LanglandsTunnell_QuatH
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_not_isGalois_fixFld_sylowH

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld sylowH mem_sylowH_iff"
namespace CubicResolventNotGalois
p2m_open "LanglandsTunnell"

open FLT.ExplicitLift LanglandsTunnell.Lift48

private def redc (z : ℤ√(-2)) : ZMod 3 := ((z.re - z.im : ℤ) : ZMod 3)

private theorem red_eq_redc (z : ℤ√(-2)) : red z = redc z := by
  rw [show z = ⟨z.re, z.im⟩ from rfl]
  simp [red, redc, Zsqrtd.lift, sub_eq_add_neg]

private theorem map_red_eq_map_redc (m : Mat) : m.map red = m.map redc := by
  ext i j; simp [Matrix.map_apply, red_eq_redc]

private def tU : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) :=
  ⟨tbar, !![-1, -1; 1, -1], by decide, by decide⟩

private def sU : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) :=
  ⟨sbar, !![0, -1; 1, -1], by decide, by decide⟩

private theorem map_redc_ne_conj :
    ∀ M ∈ P16, M.map redc ≠ ((sU * tU * sU⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
      Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
  decide

private theorem not_normal_sylowH {L : Type} [Field L] [NumberField L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : ¬ (sylowH e).Normal := by
  intro hN
  have ht : e.symm tU ∈ sylowH e := by
    rw [mem_sylowH_iff, MulEquiv.apply_symm_apply]
    refine ⟨Tlift, one_mem_P16.2.1, ?_⟩
    rw [map_red_eq_map_redc]
    decide
  have hc := hN.conj_mem _ ht (e.symm sU)
  rw [mem_sylowH_iff] at hc
  obtain ⟨M, hM, hEq⟩ := hc
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, map_red_eq_map_redc] at hEq
  exact map_redc_ne_conj M hM hEq

end LanglandsTunnell.CubicResolventNotGalois

open _root_.LanglandsTunnell _root_.P2MW.S_LanglandsTunnell_not_isGalois_fixFld_sylowH.LanglandsTunnell in
theorem solution {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    ¬ IsGalois ℚ ↥(fixFld (sylowH e)) := by
  intro hG
  refine LanglandsTunnell.CubicResolventNotGalois.not_normal_sylowH e ?_
  have h : (fixFld (sylowH e)).fixingSubgroup.Normal :=
    @IsGalois.fixingSubgroup_normal_of_isGalois ℚ L _ _ _ (fixFld (sylowH e)) _ hG
  rwa [show (fixFld (sylowH e)).fixingSubgroup = sylowH e from
    IntermediateField.fixingSubgroup_fixedField (sylowH e)] at h

end S_LanglandsTunnell_not_isGalois_fixFld_sylowH
end P2MW
export P2MW.S_LanglandsTunnell_not_isGalois_fixFld_sylowH (solution)
