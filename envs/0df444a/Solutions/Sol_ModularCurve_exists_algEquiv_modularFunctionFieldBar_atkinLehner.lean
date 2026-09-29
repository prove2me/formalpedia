-- Prove2me | solution 1 for ModularCurve.exists_algEquiv_modularFunctionFieldBar_atkinLehner
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/02ce37c6-937d-5eeb-96ac-0f1395d77039

import Mathlib
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_algEquiv_modularFunctionFieldBar_atkinLehner
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

p2m_open "ModularCurve~coeffEmb_qExpand"

namespace W7CAtkinLehnerBar

theorem coeffEmb_qExpand (L : Type*) [Field L] [Algebra ℚ L] (n : ℕ) [NeZero n]
    (x : LaurentSeries ℚ) : coeffEmb L (qExpand ℚ n x) = qExpand L n (coeffEmb L x) := by
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffEmb_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffEmb_coeff]
  · rw [coeffEmb_coeff, qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk,
      map_zero]

theorem qExpand_coeffEmb_qExpand_jq (L : Type*) [Field L] [Algebra ℚ L] (d p : ℕ) [NeZero d]
    [NeZero p] :
    qExpand L p (coeffEmb L (qExpand ℚ d jq)) = coeffEmb L (qExpand ℚ (d * p) jq) := by
  haveI : NeZero (p * d) := ⟨Nat.mul_ne_zero (NeZero.ne p) (NeZero.ne d)⟩
  rw [← coeffEmb_qExpand, qExpand_qExpand, qExpand_congr (Nat.mul_comm p d)]

end W7CAtkinLehnerBar

open W7CAtkinLehnerBar

theorem solution (N₀ p : ℕ) [NeZero N₀]
    [NeZero p] (hp : p.Prime) (hpN₀ : ¬ p ∣ N₀) :
    ∃ w : ModularCurve.modularFunctionFieldBar (N₀ * p) ≃ₐ[AlgebraicClosure ℚ]
        ModularCurve.modularFunctionFieldBar (N₀ * p),
      ∀ (d : ℕ) [NeZero d], d ∣ N₀ → ∀ x : ModularCurve.modularFunctionFieldBar (N₀ * p),
        ((x : LaurentSeries (AlgebraicClosure ℚ))
            = ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ d ModularCurve.jq) →
          ((w x : ModularCurve.modularFunctionFieldBar (N₀ * p)) : LaurentSeries (AlgebraicClosure ℚ))
            = ModularCurve.qExpand (AlgebraicClosure ℚ) p
                (ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ d ModularCurve.jq))) ∧
        ((x : LaurentSeries (AlgebraicClosure ℚ))
            = ModularCurve.qExpand (AlgebraicClosure ℚ) p
                (ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ d ModularCurve.jq)) →
          ((w x : ModularCurve.modularFunctionFieldBar (N₀ * p)) : LaurentSeries (AlgebraicClosure ℚ))
            = ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ d ModularCurve.jq)) := by
  obtain ⟨σ, hσ⟩ := ModularCurve.exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N₀ p hp hpN₀
  refine ⟨geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N₀ * p)) σ, ?_⟩
  intro d _ hd x

  set fd : modularFunctionFieldFull (N₀ * p) :=
    ⟨qExpand ℚ d jq, jqd_mem_full (N₀ * p) (Dvd.dvd.mul_right hd p)⟩ with hfd
  set fdp : modularFunctionFieldFull (N₀ * p) :=
    ⟨qExpand ℚ (d * p) jq, jqd_mem_full (N₀ * p) (Nat.mul_dvd_mul_right hd p)⟩ with hfdp
  obtain ⟨h1, h2⟩ := hσ d inferInstance hd
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · have hx' : x = ⟨coeffEmb (AlgebraicClosure ℚ) (fd : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) fd.2⟩ := Subtype.ext hx
    rw [hx', coe_geomAut_coeffEmb, qExpand_coeffEmb_qExpand_jq]
    exact congrArg (fun y : modularFunctionFieldFull (N₀ * p) =>
      coeffEmb (AlgebraicClosure ℚ) (y : LaurentSeries ℚ)) h1
  · rw [qExpand_coeffEmb_qExpand_jq] at hx
    have hx' : x = ⟨coeffEmb (AlgebraicClosure ℚ) (fdp : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) fdp.2⟩ := Subtype.ext hx
    rw [hx', coe_geomAut_coeffEmb]
    exact congrArg (fun y : modularFunctionFieldFull (N₀ * p) =>
      coeffEmb (AlgebraicClosure ℚ) (y : LaurentSeries ℚ)) h2

end S_ModularCurve_exists_algEquiv_modularFunctionFieldBar_atkinLehner
end P2MW
export P2MW.S_ModularCurve_exists_algEquiv_modularFunctionFieldBar_atkinLehner (solution)
