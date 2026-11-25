-- Prove2me | solution 1 for GlobalTheory.CongGrp.congK_basic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:02:33.939602+00:00
-- url     : https://prove2.me/submissions/78c8b0d8-f16e-4a10-9aec-50e7a6bcf144

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruentOneMatricesTransitiveNearHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MatrixCongruentOneModUniformizerPowGroupAndOrbit
import Theorems.Thm_GlobalTheory_CongGrp_mem_congK
import Theorems.Thm_GlobalTheory_CongGrp_int_mem
import Theorems.Thm_P2M_GlobalTheory_CongGrp_pow_mem__de67754d33b0
import Theorems.Thm_GlobalTheory_CongGrp_norm_one_add
import Theorems.Thm_GlobalTheory_CongGrp_vE_unit
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_UnramOrder_order_facts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.CongGrp
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable [IsNonarchimedeanLocalField F] [CharZero F]
namespace GlobalTheory.CongGrp
theorem _root_.solution (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) {m i : ℕ} (hi : 1 ≤ i)
    {A : Matrix (Fin m) (Fin m) E} (hA : A ∈ congK L ϖ m i) :
    IsUnit A.det ∧ vE L ϖ (A.det * L.cj A.det) = 0 ∧ IsIntM L A⁻¹ := by
  obtain ⟨C, hC, hAC⟩ := (mem_congK L ϖ).1 hA
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  let C' : Matrix (Fin m) (Fin m) L.O :=
    Matrix.of fun a b => ⟨algebraMap F E ((ϖ : F) ^ k) * C a b, mul_mem (pow_mem' L ϖ k) (hC a b)⟩
  let p : L.O := ⟨algebraMap F E (ϖ : F), int_mem L ϖ⟩
  let A' : Matrix (Fin m) (Fin m) L.O := 1 + p • C'
  have hAA : A = L.O.subtype.mapMatrix A' := by
    rw [hAC]
    simp only [A', map_add, map_one]
    congr 1
    ext a b
    simp [C', p, pow_succ]
    ring
  obtain ⟨y, hy⟩ : ∃ y : L.O, A'.det = 1 + p * y := by
    refine ⟨C'.trace + Polynomial.eval p (1 + (Polynomial.X : Polynomial L.O) •
      C'.map Polynomial.C).det.divX.divX * p, ?_⟩
    simp only [A']
    rw [Matrix.det_one_add_smul]
    ring
  have hdet : A.det = 1 + algebraMap F E (ϖ : F) * (y : E) := by
    rw [hAA, ← RingHom.map_det, hy]
    rfl
  obtain ⟨u, hu⟩ := norm_one_add L ϖ hϖ y.2
  have e3 : ((u : 𝒪[F]) : F) * ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) = 1 := by
    rw [← Subring.coe_mul]; simp
  have hcj : L.cj (1 + algebraMap F E (ϖ : F) * (y : E)) ∈ L.O :=
    ((GlobalTheory.UnramOrder.order_facts L ϖ hϖ).2.1 _
      (add_mem (one_mem _) (mul_mem (int_mem L ϖ) y.2))).1
  have hU : IsUnit A'.det := by
    refine IsUnit.of_mul_eq_one
      (⟨_, mul_mem hcj (int_mem L ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]))⟩ : L.O) ?_
    rw [hy]
    apply Subtype.ext
    change (1 + algebraMap F E (ϖ : F) * (y : E)) * (_ * _) = 1
    rw [← mul_assoc, hu, ← map_mul, e3, map_one]
  refine ⟨?_, ?_, ?_⟩
  · rw [hAA, ← RingHom.map_det]
    exact hU.map _
  · rw [hdet, hu]
    exact vE_unit L ϖ hϖ u
  · have : A⁻¹ = L.O.subtype.mapMatrix A'⁻¹ := by
      apply Matrix.inv_eq_right_inv
      rw [hAA, ← map_mul, Matrix.mul_nonsing_inv _ hU, map_one]
    rw [this]
    intro a b
    exact (A'⁻¹ a b).2
end GlobalTheory.CongGrp
