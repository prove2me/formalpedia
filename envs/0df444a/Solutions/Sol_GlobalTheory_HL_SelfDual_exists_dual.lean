-- Prove2me | solution 1 for GlobalTheory.HL.SelfDual.exists_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:38:53.746967+00:00
-- url     : https://prove2.me/submissions/288ccc95-f67c-404e-82dc-993a79c8bf09

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.SelfDual
open Matrix GlobalTheory.HL.Eichler GlobalTheory.UnramOrder
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.SelfDual
theorem _root_.solution (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (hH : IsUnit Hm.det)
    {b : Fin n → Fin n → E} (hb : Submodule.span E (Set.range b) = ⊤) :
    ∃ y : Fin n → Fin n → E, ∀ i j, hf L Hm (b i) (y j) = if i = j then 1 else 0 := by
  have h1 : ∀ i, ∃ a : Fin n → E, ∑ k, a k • b k = Pi.single i 1 := fun i =>
    (Submodule.mem_span_range_iff_exists_fun E).1 (hb ▸ Submodule.mem_top)
  choose C hC using h1
  have h2 : Matrix.of C * Matrix.of b = 1 := by
    ext i j
    have := congrFun (hC i) j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.of_apply, this, Pi.single_apply, eq_comm]
  have h3 : Matrix.of b * Hm * (Hm⁻¹ * Matrix.of C) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hH, mul_eq_one_comm.1 h2]
  refine ⟨fun j k => L.cj ((Hm⁻¹ * Matrix.of C) k j), fun i j => ?_⟩
  rw [← Matrix.one_apply, ← h3, Matrix.mul_apply]
  simp only [hf, L.cj_cj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_apply (M := Matrix.of b), Finset.sum_mul]
  rfl
end GlobalTheory.HL.SelfDual
