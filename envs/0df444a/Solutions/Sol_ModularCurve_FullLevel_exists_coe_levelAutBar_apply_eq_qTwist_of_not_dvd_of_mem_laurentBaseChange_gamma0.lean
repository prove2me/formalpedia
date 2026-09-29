-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_coe_levelAutBar_apply_eq_qTwist_of_not_dvd_of_mem_laurentBaseChange_gamma0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/eae887cf-c767-5eea-b756-baacb5666005

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qTwist_of_redQ_eq_unipotent
import Theorems.Thm_ModularCurve_FullLevel_levelAutBar_mul
import Theorems.Thm_ModularCurve_FullLevel_levelAutBar_apply_eq_self_of_dvd_of_coe_mem_laurentBaseChange_gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_coe_levelAutBar_apply_eq_qTwist_of_not_dvd_of_mem_laurentBaseChange_gamma0
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel CongruenceSubgroup
open scoped MatrixGroups

namespace A1ellE121

private def unip (t : ℤ) : SL(2, ℤ) :=
  ⟨!![1, t; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩

private theorem unip_mem_gamma0 (M' : ℕ) (t : ℤ) : unip t ∈ Gamma0 M' := by
  rw [Gamma0_mem]
  simp [unip]

private theorem redQ_unip (q : ℕ) [Fact q.Prime] (t : ℤ) :
    redQ q (unip t) = CuspidalType.unipotent q (t : ZMod q) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [redQ, unip, CuspidalType.unipotent, Matrix.SpecialLinearGroup.toGL]

private def split (γ : SL(2, ℤ)) (t : ℤ) : SL(2, ℤ) :=
  ⟨!![γ 0 0, γ 0 1 - γ 0 0 * t; γ 1 0, γ 1 1 - γ 1 0 * t], by
    rw [Matrix.det_fin_two_of]
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at h
    linear_combination h⟩

private theorem split_mul_unip (γ : SL(2, ℤ)) (t : ℤ) : split γ t * unip t = γ := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [split, unip, Matrix.mul_apply, Fin.sum_univ_two]

private theorem split_mem_gamma0 (M' : ℕ) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (t : ℤ) :
    split γ t ∈ Gamma0 M' := by
  rw [Gamma0_mem] at hγ ⊢
  simpa [split] using hγ

end A1ellE121

open A1ellE121 in

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (ζ : Idx q)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (ha : ¬ (q : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0)
    (u : (AlgebraicClosure ℚ)ˣ) (hu : (u : AlgebraicClosure ℚ) = ζ.val) :
    ∃ k : ℤ, ∀ (g : LaurentSeries (AlgebraicClosure ℚ)),
      g ∈ laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')) →
      ∀ (x : fieldBar q M'), (x : LaurentSeries (AlgebraicClosure ℚ)) = g →
        ((levelAutBar q M' ζ γ x : fieldBar q M') : LaurentSeries (AlgebraicClosure ℚ)) =
          ModularCurve.qTwist (u ^ k) g := by

  have ha0 : ((γ 0 0 : ℤ) : ZMod q) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  set t₀ : ZMod q := ((γ 0 1 : ℤ) : ZMod q) / ((γ 0 0 : ℤ) : ZMod q) with ht₀
  set t : ℤ := (t₀.val : ℤ) with ht
  have htcast : ((t : ℤ) : ZMod q) = t₀ := by
    rw [ht, Int.cast_natCast, ZMod.natCast_zmod_val]

  have hγ₁ : split γ t ∈ Gamma0 M' := split_mem_gamma0 M' γ hγ t
  have hβ : unip t ∈ Gamma0 M' := unip_mem_gamma0 M' t
  have hb : (q : ℤ) ∣ ((split γ t : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    show (((γ 0 1 - γ 0 0 * t : ℤ)) : ZMod q) = 0
    push_cast
    rw [htcast, ht₀, mul_div_cancel₀ _ ha0, sub_self]
  refine ⟨t, fun g hg x hx => ?_⟩
  have hmul := levelAutBar_mul q M' hqM' ζ (split γ t) (unip t) hγ₁ hβ
  rw [split_mul_unip] at hmul
  rw [hmul, AlgEquiv.trans_apply,
    levelAutBar_apply_eq_self_of_dvd_of_coe_mem_laurentBaseChange_gamma0 q M' hqM' ζ (split γ t) hγ₁ hb g hg x hx]
  have htw := coe_levelAutBar_apply_eq_qTwist_of_redQ_eq_unipotent q M' hqM' ζ (unip t) hβ
    ⟨(t : ZMod q), redQ_unip q t⟩ u hu x
  rw [htw, hx]
  rfl

end S_ModularCurve_FullLevel_exists_coe_levelAutBar_apply_eq_qTwist_of_not_dvd_of_mem_laurentBaseChange_gamma0
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_coe_levelAutBar_apply_eq_qTwist_of_not_dvd_of_mem_laurentBaseChange_gamma0 (solution)
