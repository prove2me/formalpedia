-- Prove2me | solution 1 for ModularCurve.geomAut_atkinLehner_comp_legs
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/1e453501-a103-5989-8fec-ed0230951689

import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_GeometricBaseChange
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_geomAut_atkinLehner_comp_legs

set_option autoImplicit false

noncomputable section

open ModularCurve

namespace AL2Sol

variable (N ℓ : ℕ) [NeZero N] [NeZero ℓ]
variable (σ : modularFunctionFieldFull (N * ℓ) ≃ₐ[ℚ] modularFunctionFieldFull (N * ℓ))
variable (hσ : IsAtkinLehnerAutFull N ℓ σ)

theorem mem_roof {x : LaurentSeries ℚ} (hx : x ∈ modularFunctionFieldFull N) : x ∈ modularFunctionFieldFull (N * ℓ) :=
  full_degeneracy_le (dvd_mul_right N ℓ) hx

omit [NeZero N] in

theorem qExpand_mem_roof {x : LaurentSeries ℚ} (hx : x ∈ modularFunctionFieldFull N) :
    qExpand ℚ ℓ x ∈ modularFunctionFieldFull (N * ℓ) :=
  full_degeneracy_map_le (N := N) ℓ ⟨x, hx, rfl⟩

include hσ in

theorem coe_sigma_of_mem {x : LaurentSeries ℚ} (hx : x ∈ modularFunctionFieldFull N) :
    ((σ ⟨x, mem_roof N ℓ hx⟩ : modularFunctionFieldFull (N * ℓ)) : LaurentSeries ℚ) = qExpand ℚ ℓ x := by
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy =>
      obtain ⟨d, hd0, hd, rfl⟩ := hy
      haveI := hd0
      have h := (hσ d hd0 hd).1
      have e : (⟨qExpand ℚ d jq, mem_roof N ℓ (jqd_mem_full N hd)⟩ : modularFunctionFieldFull (N * ℓ)) =
          ⟨qExpand ℚ d jq, jqd_mem_full (N * ℓ) (Dvd.dvd.mul_right hd ℓ)⟩ := rfl
      rw [e, h]
      show qExpand ℚ (d * ℓ) jq = qExpand ℚ ℓ (qExpand ℚ d jq)
      rw [qExpand_qExpand]
      exact qExpand_congr (Nat.mul_comm d ℓ) jq
  | algebraMap r =>
      have hr : (⟨algebraMap ℚ (LaurentSeries ℚ) r, mem_roof N ℓ ((modularFunctionFieldFull N).algebraMap_mem r)⟩ :
          modularFunctionFieldFull (N * ℓ)) = (r : modularFunctionFieldFull (N * ℓ)) := by
        apply Subtype.ext
        show algebraMap ℚ (LaurentSeries ℚ) r = ((r : modularFunctionFieldFull (N * ℓ)) : LaurentSeries ℚ)
        rw [eq_ratCast (algebraMap ℚ (LaurentSeries ℚ)) r]
        norm_cast
      rw [hr, map_ratCast]
      push_cast
      rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero, ← algebraMap_laurentSeries_eq_single,
        eq_ratCast]
  | add x y hx hy ihx ihy =>
      have e : (⟨x + y, mem_roof N ℓ (add_mem hx hy)⟩ : modularFunctionFieldFull (N * ℓ)) =
          ⟨x, mem_roof N ℓ hx⟩ + ⟨y, mem_roof N ℓ hy⟩ := rfl
      rw [e, map_add, IntermediateField.coe_add, ihx, ihy, map_add]
  | inv x hx ih =>
      have e : (⟨x⁻¹, mem_roof N ℓ (inv_mem hx)⟩ : modularFunctionFieldFull (N * ℓ)) = (⟨x, mem_roof N ℓ hx⟩)⁻¹ := rfl
      rw [e, map_inv₀, IntermediateField.coe_inv, ih, map_inv₀]
  | mul x y hx hy ihx ihy =>
      have e : (⟨x * y, mem_roof N ℓ (mul_mem hx hy)⟩ : modularFunctionFieldFull (N * ℓ)) =
          ⟨x, mem_roof N ℓ hx⟩ * ⟨y, mem_roof N ℓ hy⟩ := rfl
      rw [e, map_mul, IntermediateField.coe_mul, ihx, ihy, map_mul]

omit [NeZero N] in
include hσ in

theorem coe_sigma_qExpand_of_mem {x : LaurentSeries ℚ} (hx : x ∈ modularFunctionFieldFull N) :
    ((σ ⟨qExpand ℚ ℓ x, qExpand_mem_roof N ℓ hx⟩ : modularFunctionFieldFull (N * ℓ)) : LaurentSeries ℚ) = x := by
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy =>
      obtain ⟨d, hd0, hd, rfl⟩ := hy
      haveI := hd0
      have h := (hσ d hd0 hd).2
      have e : (⟨qExpand ℚ ℓ (qExpand ℚ d jq), qExpand_mem_roof N ℓ (jqd_mem_full N hd)⟩ :
            modularFunctionFieldFull (N * ℓ)) =
          ⟨qExpand ℚ (d * ℓ) jq, jqd_mem_full (N * ℓ) (Nat.mul_dvd_mul_right hd ℓ)⟩ :=
        Subtype.ext ((qExpand_qExpand d ℓ jq).trans (qExpand_congr (Nat.mul_comm ℓ d) jq))
      rw [e, h]
  | algebraMap r =>
      have hr : (⟨qExpand ℚ ℓ (algebraMap ℚ (LaurentSeries ℚ) r),
            qExpand_mem_roof N ℓ ((modularFunctionFieldFull N).algebraMap_mem r)⟩ :
          modularFunctionFieldFull (N * ℓ)) = (r : modularFunctionFieldFull (N * ℓ)) := by
        apply Subtype.ext
        show qExpand ℚ ℓ (algebraMap ℚ (LaurentSeries ℚ) r) = ((r : modularFunctionFieldFull (N * ℓ)) : LaurentSeries ℚ)
        rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero, ← algebraMap_laurentSeries_eq_single,
          eq_ratCast (algebraMap ℚ (LaurentSeries ℚ)) r]
        norm_cast
      rw [hr, map_ratCast]
      push_cast
      exact (eq_ratCast (algebraMap ℚ (LaurentSeries ℚ)) r).symm
  | add x y hx hy ihx ihy =>
      have e : (⟨qExpand ℚ ℓ (x + y), qExpand_mem_roof N ℓ (add_mem hx hy)⟩ : modularFunctionFieldFull (N * ℓ)) =
          ⟨qExpand ℚ ℓ x, qExpand_mem_roof N ℓ hx⟩ + ⟨qExpand ℚ ℓ y, qExpand_mem_roof N ℓ hy⟩ :=
        Subtype.ext (map_add (qExpand ℚ ℓ) x y)
      rw [e, map_add, IntermediateField.coe_add, ihx, ihy]
  | inv x hx ih =>
      have e : (⟨qExpand ℚ ℓ x⁻¹, qExpand_mem_roof N ℓ (inv_mem hx)⟩ : modularFunctionFieldFull (N * ℓ)) =
          (⟨qExpand ℚ ℓ x, qExpand_mem_roof N ℓ hx⟩)⁻¹ :=
        Subtype.ext (map_inv₀ (qExpand ℚ ℓ) x)
      rw [e, map_inv₀, IntermediateField.coe_inv, ih]
  | mul x y hx hy ihx ihy =>
      have e : (⟨qExpand ℚ ℓ (x * y), qExpand_mem_roof N ℓ (mul_mem hx hy)⟩ : modularFunctionFieldFull (N * ℓ)) =
          ⟨qExpand ℚ ℓ x, qExpand_mem_roof N ℓ hx⟩ * ⟨qExpand ℚ ℓ y, qExpand_mem_roof N ℓ hy⟩ :=
        Subtype.ext (map_mul (qExpand ℚ ℓ) x y)
      rw [e, map_mul, IntermediateField.coe_mul, ihx, ihy]

variable (L : Type*) [Field L] [Algebra ℚ L] [Algebra.IsAlgebraic ℚ L]

omit [NeZero N] [Algebra.IsAlgebraic ℚ L] in

theorem algHom_ext_coeffEmb {E : IntermediateField L (LaurentSeries L)}
    {f g : laurentBaseChange L (modularFunctionFieldFull N) →ₐ[L] E}
    (h : ∀ (x : LaurentSeries ℚ) (hx : x ∈ modularFunctionFieldFull N),
      f ⟨coeffEmb L x, coeffEmb_mem_laurentBaseChange L hx⟩ = g ⟨coeffEmb L x, coeffEmb_mem_laurentBaseChange L hx⟩) :
    f = g := by
  apply AlgHom.ext
  rintro ⟨z, hz⟩
  induction hz using IntermediateField.adjoin_induction with
  | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      exact h x hx
  | algebraMap r =>
      have e : (⟨algebraMap L (LaurentSeries L) r, (laurentBaseChange L (modularFunctionFieldFull N)).algebraMap_mem r⟩ :
          laurentBaseChange L (modularFunctionFieldFull N)) = algebraMap L _ r := rfl
      rw [e, AlgHom.commutes, AlgHom.commutes]
  | add x y hx hy ihx ihy =>
      have e : (⟨x + y, add_mem hx hy⟩ : laurentBaseChange L (modularFunctionFieldFull N)) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [e, map_add, map_add, ihx, ihy]
  | inv x hx ih =>
      have e : (⟨x⁻¹, inv_mem hx⟩ : laurentBaseChange L (modularFunctionFieldFull N)) = (⟨x, hx⟩)⁻¹ := rfl
      rw [e, map_inv₀, map_inv₀, ih]
  | mul x y hx hy ihx ihy =>
      have e : (⟨x * y, mul_mem hx hy⟩ : laurentBaseChange L (modularFunctionFieldFull N)) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [e, map_mul, map_mul, ihx, ihy]

include hσ in

theorem geomAut_comp_alpha :
    (geomAut L (modularFunctionFieldFull (N * ℓ)) σ).toAlgHom.comp (heckeAlphaBar L N ℓ) = heckeBetaBar L N ℓ := by
  refine algHom_ext_coeffEmb N L (fun x hx => ?_)
  apply Subtype.ext
  rw [AlgHom.comp_apply]
  have eα : heckeAlphaBar L N ℓ ⟨coeffEmb L x, coeffEmb_mem_laurentBaseChange L hx⟩ =
      ⟨coeffEmb L ((⟨x, mem_roof N ℓ hx⟩ : modularFunctionFieldFull (N * ℓ)) : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange L (mem_roof N ℓ hx)⟩ :=
    Subtype.ext (by simp)
  rw [eα]
  show ((geomAut L (modularFunctionFieldFull (N * ℓ)) σ
      ⟨coeffEmb L ((⟨x, mem_roof N ℓ hx⟩ : modularFunctionFieldFull (N * ℓ)) : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange L (⟨x, mem_roof N ℓ hx⟩ : modularFunctionFieldFull (N * ℓ)).2⟩ :
      laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) : LaurentSeries L) =
    qExpand L ℓ (coeffEmb L x)
  rw [geomAut_coeffEmb]
  show coeffEmb L ((σ ⟨x, mem_roof N ℓ hx⟩ : modularFunctionFieldFull (N * ℓ)) : LaurentSeries ℚ) = qExpand L ℓ (coeffEmb L x)
  rw [coe_sigma_of_mem N ℓ σ hσ hx]
  exact coeffMap_qExpand (algebraMap ℚ L) ℓ x

include hσ in

theorem geomAut_comp_beta :
    (geomAut L (modularFunctionFieldFull (N * ℓ)) σ).toAlgHom.comp (heckeBetaBar L N ℓ) = heckeAlphaBar L N ℓ := by
  refine algHom_ext_coeffEmb N L (fun x hx => ?_)
  apply Subtype.ext
  rw [AlgHom.comp_apply]
  have eβ : heckeBetaBar L N ℓ ⟨coeffEmb L x, coeffEmb_mem_laurentBaseChange L hx⟩ =
      ⟨coeffEmb L ((⟨qExpand ℚ ℓ x, qExpand_mem_roof N ℓ hx⟩ : modularFunctionFieldFull (N * ℓ)) : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange L (qExpand_mem_roof N ℓ hx)⟩ := by
    apply Subtype.ext
    rw [coe_heckeBetaBar]
    exact (coeffMap_qExpand (algebraMap ℚ L) ℓ x).symm
  rw [eβ]
  show ((geomAut L (modularFunctionFieldFull (N * ℓ)) σ
      ⟨coeffEmb L ((⟨qExpand ℚ ℓ x, qExpand_mem_roof N ℓ hx⟩ : modularFunctionFieldFull (N * ℓ)) : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange L (⟨qExpand ℚ ℓ x, qExpand_mem_roof N ℓ hx⟩ : modularFunctionFieldFull (N * ℓ)).2⟩ :
      laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) : LaurentSeries L) =
    ((heckeAlphaBar L N ℓ ⟨coeffEmb L x, coeffEmb_mem_laurentBaseChange L hx⟩ :
      laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) : LaurentSeries L)
  rw [geomAut_coeffEmb, coe_heckeAlphaBar]
  show coeffEmb L ((σ ⟨qExpand ℚ ℓ x, qExpand_mem_roof N ℓ hx⟩ : modularFunctionFieldFull (N * ℓ)) : LaurentSeries ℚ) =
    coeffEmb L x
  rw [coe_sigma_qExpand_of_mem N ℓ σ hσ hx]

end AL2Sol

end

open ModularCurve in

theorem solution (L : Type*) [Field L] [Algebra ℚ L] [Algebra.IsAlgebraic ℚ L] (N ℓ : ℕ) [NeZero N] [NeZero ℓ] (σ : modularFunctionFieldFull (N * ℓ) ≃ₐ[ℚ] modularFunctionFieldFull (N * ℓ)) (hσ : IsAtkinLehnerAutFull N ℓ σ) : (geomAut L (modularFunctionFieldFull (N * ℓ)) σ).toAlgHom.comp (heckeAlphaBar L N ℓ) = heckeBetaBar L N ℓ ∧ (geomAut L (modularFunctionFieldFull (N * ℓ)) σ).toAlgHom.comp (heckeBetaBar L N ℓ) = heckeAlphaBar L N ℓ :=
  ⟨AL2Sol.geomAut_comp_alpha N ℓ σ hσ L, AL2Sol.geomAut_comp_beta N ℓ σ hσ L⟩

end S_ModularCurve_geomAut_atkinLehner_comp_legs
end P2MW
export P2MW.S_ModularCurve_geomAut_atkinLehner_comp_legs (solution)
