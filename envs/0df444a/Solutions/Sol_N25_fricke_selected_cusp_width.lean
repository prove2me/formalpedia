-- Prove2me | solution 1 for N25.fricke_selected_cusp_width
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:57:58.647467+00:00
-- url     : https://prove2.me/submissions/de559010-601a-45b8-b457-8a1a026eb4a2

import Mathlib
import Definitions.Def_N25_SelectedCusps
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_N25_jqTwentyFive_mem_xH25
import Definitions.Def_N25
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Theorems.Thm_N25_gamma_field_fixes_gamma0
import Theorems.Thm_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero
import Theorems.Thm_ModularCurve_diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply
import Theorems.Thm_ModularCurve_ord_qInftyPlaceBar
import Theorems.Thm_ModularCurve_order_jqModC

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open ModularCurve AlgebraicCurve

namespace N25

open Endgame

private theorem order_eq_of_coeff {R : Type*} [CommRing R] {x : LaurentSeries R} {m : ℤ}
    (hm : x.coeff m ≠ 0) (hlt : ∀ k < m, x.coeff k = 0) : x.order = m := by
  have hx : x ≠ 0 := fun h => hm (by simp [h])
  apply le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hm)
  by_contra hlt'
  exact (fun h => hx (HahnSeries.coeff_order_eq_zero.mp h)) (hlt _ (not_le.mp hlt'))

private theorem order_qExpand (N : ℕ) [NeZero N] {R : Type*} [CommRing R] {y : LaurentSeries R}
    (hy : y ≠ 0) :
    (ModularCurve.qExpand R N y).order = N * y.order := by
  apply order_eq_of_coeff
  · rw [ModularCurve.qExpand_coeff_mul]
    exact fun h => hy (HahnSeries.coeff_order_eq_zero.mp h)
  · intro k hk
    by_cases hdvd : (N : ℤ) ∣ k
    · obtain ⟨k', rfl⟩ := hdvd
      rw [ModularCurve.qExpand_coeff_mul]
      apply HahnSeries.coeff_eq_zero_of_lt_order
      have hN0 : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
      nlinarith
    · exact ModularCurve.qExpand_coeff_of_not_dvd N y hdvd

private theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (n : ℕ) [NeZero n] (x : LaurentSeries R) :
    coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases h : (n : ℤ) ∣ k
  · obtain ⟨m,rfl⟩ := h
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd _ _ h, qExpand_coeff_of_not_dvd _ _ h, map_zero]

/-- Inverse Fricke images of the five selected cusps have exact j-pole order twenty-five. -/
theorem _root_.solution
    (w : FG ≃ₐ[Qbar] FG)
    (hw : (w (emb25 j25) : LaurentSeries Qbar) = jqNModC Qbar 25) (i : Fin 5) :
    (SemilinearAut.ofAlgAut w.symm • pG25 i).ord (emb25 j25) = -25 := by
  let jN : FQ := ⟨jqNModC ℚ 25,jqTwentyFive_mem_xH25 ℚ⟩
  let xN : FG := emb25 jN
  have hxN : (xN : LaurentSeries Qbar) = jqNModC Qbar 25 := by
    change coeffMap (algebraMap ℚ Qbar) (qExpand ℚ 25 (jqModC ℚ)) = _
    rw [coeffMap_qExpand]
    congr 1
    exact map_jqModC _
  have hxΓ0 : (xN : LaurentSeries Qbar) ∈
      laurentBaseChange Qbar (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 25)) := by
    apply coeffEmb_mem_laurentBaseChange
    apply modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ 25
    exact jqModCd_mem_full ℚ 25 (dvd_refl 25)
  have hfix : (SemilinearAut.ofAlgAut gammaF25)^i.val • xN = xN := by
    rw [← map_pow, SemilinearAut.ofAlgAut_smul]
    exact gamma_field_fixes_gamma0 i.val xN hxΓ0
  have ho := SemilinearAut.ord_smul ((SemilinearAut.ofAlgAut gammaF25)^i.val)
    (qInftyPlaceBar Qbar FG cuspChoice25.hG) xN
  rw [hfix, ord_qInftyPlaceBar] at ho
  change (pG25 i).ord xN = _ at ho
  have hq : (qSeriesBar Qbar FG xN).order = -25 := by
    change (xN : LaurentSeries Qbar).order = -25
    rw [hxN, jqNModC, order_qExpand]
    · rw [order_jqModC]; norm_num
    · intro hz
      have hj := order_jqModC Qbar
      rw [hz, HahnSeries.order_zero] at hj
      norm_num at hj
  rw [hq] at ho
  have hwN : w (emb25 j25) = xN := Subtype.ext (hw.trans hxN.symm)
  have h := SemilinearAut.ord_smul (SemilinearAut.ofAlgAut w.symm) (pG25 i) (w (emb25 j25))
  rw [SemilinearAut.ofAlgAut_smul, AlgEquiv.symm_apply_apply, hwN, ho] at h
  exact h

end N25
