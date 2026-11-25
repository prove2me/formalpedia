-- Prove2me | solution 1 for GlobalTheory.HL.OrthCompl.exists_norm_one_orth_triple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:18:55.629798+00:00
-- url     : https://prove2.me/submissions/8d9b8ffc-813c-4021-8f5c-96c47501b47e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsNormOneOrthTriple
import Theorems.Thm_GlobalTheory_HL_OrthCompl_exists_norm_one_orth
import Theorems.Thm_GlobalTheory_HL_OrthCompl_exists_primitive
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_mem_iff
import Theorems.Thm_GlobalTheory_UnramOrder_cj_mem
import Theorems.Thm_GlobalTheory_UnramOrder_exists_norm
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.OrthCompl
open GlobalTheory.HL.Eichler GlobalTheory.UnramOrder
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E}
variable [IsNonarchimedeanLocalField F] [CharZero F]
namespace GlobalTheory.HL.OrthCompl
theorem _root_.solution (y0 y1 y2 : E) :
    ∃ u0 ∈ L.O, ∃ u1 ∈ L.O, ∃ u2 ∈ L.O, u0 * L.cj u0 + u1 * L.cj u1 + u2 * L.cj u2 = 1 ∧
      u0 * y0 + u1 * y1 + u2 * y2 = 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨h1, -, -, h4, -, -, -, h8⟩ := order_facts L ϖ hϖ
  have := L.reduced
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; omega)
  have : IsArtinianRing E := IsArtinianRing.of_finite F E
  have hden : ∀ x : E, ∃ a : 𝒪[F], a ≠ 0 ∧ algebraMap F E a * x ∈ L.O := fun x => by
    obtain ⟨a, ha, hi⟩ := ((IsFractionRing.isAlgebraic_iff 𝒪[F] F E).2
      (Algebra.IsAlgebraic.isAlgebraic x)).exists_integral_multiple
    refine ⟨a, ha, (L.O_def _).2 ?_⟩
    rwa [Algebra.smul_def] at hi
  have hint : ∀ a : 𝒪[F], algebraMap F E a ∈ L.O := fun a => (algebraMap_mem_iff L a).2 a.2
  obtain ⟨a0, ha0, hy0⟩ := hden y0
  obtain ⟨a1, ha1, hy1⟩ := hden y1
  obtain ⟨a2, ha2, hy2⟩ := hden y2
  have hid : ∀ e : E, e * e = e → e ∈ L.O := fun e he => by
    rw [L.O_def]
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, by monicity!, ?_⟩
    simp [sq, he]
  obtain ⟨d, b0, hb0, b1, hb1, b2, hb2, r0, hr0, r1, hr1, r2, hr2, e0, e1, e2, e3⟩ :=
    exists_primitive L.O hid (L.O.mul_mem (L.O.mul_mem (hint a1) (hint a2)) hy0)
      (L.O.mul_mem (L.O.mul_mem (hint a0) (hint a2)) hy1)
      (L.O.mul_mem (L.O.mul_mem (hint a0) (hint a1)) hy2)
  obtain ⟨u0, hu0, u1, hu1, u2, hu2, k1, k2⟩ := exists_norm_one_orth L.O (L.cj : E →+* E)
    (algebraMap 𝒪[F] E) L.cj_cj (fun x hx => cj_mem L hx) (fun x hx => exists_norm L hx)
    (by simpa using h1 1) h8 (cj_mem L hb0) (cj_mem L hb1) (cj_mem L hb2) hr0 hr1 hr2
    (by simpa using congrArg L.cj e3)
  refine ⟨u0, hu0, u1, hu1, u2, hu2, k1, ?_⟩
  simp only [RingHom.coe_coe, L.cj_cj] at k2
  have hne : (a0 : F) * a1 * a2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by simpa using ha0) (by simpa using ha1)) (by simpa using ha2)
  refine ((IsUnit.mk0 _ hne).map (algebraMap F E)).mul_right_eq_zero.1 ?_
  simp only [map_mul]
  linear_combination u0 * e0 + u1 * e1 + u2 * e2 + d * k2
end GlobalTheory.HL.OrthCompl
