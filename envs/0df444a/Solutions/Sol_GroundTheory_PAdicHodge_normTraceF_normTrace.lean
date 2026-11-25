-- Prove2me | solution 1 for GroundTheory.PAdicHodge.normTraceF_normTrace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:18:59.725397+00:00
-- url     : https://prove2.me/submissions/c011da72-b60e-43dd-af9c-3277651262a5

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.normTraceFₗ_apply
attribute [local simp] GroundTheory.PAdicHodge.normTraceₗ_apply
attribute [local simp] GroundTheory.PAdicHodge.normTrace_zero

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial Module IntermediateField
noncomputable section
variable (F : Type*) {Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
variable [CharZero F] [Algebra.IsIntegral F Ω]
namespace GroundTheory.PAdicHodge
theorem _root_.solution (E : Type*) [Field E] [Algebra F E] [Algebra E Ω]
    [IsScalarTower F E Ω] [FiniteDimensional F E] (y : Ω) :
    normTraceF F (normTrace E y) = normTraceF F y := by
  haveI : Algebra.IsIntegral E Ω := Algebra.IsIntegral.tower_top F
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  have hyE : IsIntegral E y := Algebra.IsIntegral.isIntegral y
  haveI : FiniteDimensional E E⟮y⟯ := IntermediateField.adjoin.finiteDimensional hyE
  haveI : FiniteDimensional F E⟮y⟯ := FiniteDimensional.trans F E E⟮y⟯
  haveI : IsScalarTower F E⟮y⟯ Ω := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply F E Ω, IsScalarTower.algebraMap_apply F E E⟮y⟯]; rfl
  set g : E⟮y⟯ := AdjoinSimple.gen E y
  have hE : normTraceF E y = Algebra.trace E E⟮y⟯ g / (finrank E E⟮y⟯ : E) :=
    normTraceF_eq_trace_div E (Ω := Ω) E⟮y⟯ g
  have hFy : normTraceF F y = Algebra.trace F E⟮y⟯ g / (finrank F E⟮y⟯ : F) :=
    normTraceF_eq_trace_div F (Ω := Ω) E⟮y⟯ g
  have hF : (finrank E E⟮y⟯ : F) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hFE : (finrank F E : F) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have key : normTrace E y =
      ((finrank E E⟮y⟯ : F)⁻¹) • algebraMap E Ω (Algebra.trace E E⟮y⟯ g) := by
    rw [normTrace, hE, div_eq_inv_mul, map_mul, Algebra.smul_def,
      IsScalarTower.algebraMap_apply F E Ω]
    congr 2
    simp
  have hT : normTraceF F (algebraMap E Ω (Algebra.trace E E⟮y⟯ g)) =
      Algebra.trace F E (Algebra.trace E E⟮y⟯ g) / (finrank F E : F) :=
    normTraceF_eq_trace_div F (Ω := Ω) E _
  rw [key, normTraceF_smul, hT, hFy, Algebra.trace_trace, ← Module.finrank_mul_finrank F E E⟮y⟯]
  push_cast
  field_simp
end GroundTheory.PAdicHodge
