-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.det_adUnipotent_of_mem_borel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:13:26.215917+00:00
-- url     : https://prove2.me/submissions/28ef24a0-d6c6-4cc2-9800-15ace9a72d99

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
import Theorems.Thm_GroundTheory_Automorphic_Measures_mul_single_mul_apply
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_Measures_coe_unipotentCoord_symm_single
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk


attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply

set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel Iwasawa
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.Measures
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {F n β}
variable (F n β)
variable {F n β}
namespace GroundTheory.Automorphic.Measures
theorem _root_.solution (p : blockUpper F n β)
    (hp : (p : GL (Fin n) F) ∈ borel F n) :
    (LinearEquiv.det (adUnipotent p) : F) = ∏ s : UnipotentIndex n β,
      ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.1 s.1.1 *
        (((p : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.2 s.1.2 := by
  classical
  set P : Matrix (Fin n) (Fin n) F := ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  set Q : Matrix (Fin n) (Fin n) F :=
    (((p : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  have hP : P.IsUpperTriangular := hp
  have hQ : Q.IsUpperTriangular := (borel F n).inv_mem hp
  let A : (UnipotentIndex n β → F) →ₗ[F] (UnipotentIndex n β → F) :=
    (((unipotentCoord F n β).symm.trans ((adUnipotent p).trans (unipotentCoord F n β))) :
      (UnipotentIndex n β → F) →ₗ[F] (UnipotentIndex n β → F))
  have hdet : (LinearEquiv.det (adUnipotent p) : F) = LinearMap.det A := by
    rw [← LinearEquiv.det_conj (adUnipotent p) (unipotentCoord F n β), LinearEquiv.coe_det]
    rfl
  have hM : ∀ s t, LinearMap.toMatrix' A s t = P s.1.1 t.1.1 * Q t.1.2 s.1.2 := by
    intro s t
    rw [LinearMap.toMatrix'_apply]
    show ((adUnipotent p ((unipotentCoord F n β).symm (Pi.single t 1)) : lieUnipotent F n β) :
      Matrix (Fin n) (Fin n) F) s.1.1 s.1.2 = _
    rw [coe_adUnipotent, coe_unipotentCoord_symm_single, mul_single_mul_apply]
  let κ : UnipotentIndex n β → Lex (Fin n × (Fin n)ᵒᵈ) :=
    fun s => toLex (s.1.1, OrderDual.toDual s.1.2)
  have hκ : Function.Injective κ := by
    intro s t h
    simp only [κ, toLex_inj, Prod.mk.injEq, OrderDual.toDual_inj] at h
    exact Subtype.ext (Prod.ext h.1 h.2)
  have hBT : (LinearMap.toMatrix' A).BlockTriangular κ := by
    intro s t hts
    rw [hM]
    rcases Prod.Lex.lt_iff.1 hts with h | ⟨h1, h2⟩
    · have h' : t.1.1 < s.1.1 := h
      rw [hP h', zero_mul]
    · have h' : s.1.2 < t.1.2 := h2
      rw [hQ h', mul_zero]
  rw [hdet, ← LinearMap.det_toMatrix', hBT.det, Finset.prod_image fun s _ t _ h => hκ h]
  refine Finset.prod_congr rfl fun s _ => ?_
  let : Unique {t // κ t = κ s} :=
    ⟨⟨⟨s, rfl⟩⟩, fun t => Subtype.ext (hκ t.2)⟩
  rw [Matrix.det_unique]
  show LinearMap.toMatrix' A (default : {t // κ t = κ s}).1 (default : {t // κ t = κ s}).1 = _
  rw [hM]
  rfl
end GroundTheory.Automorphic.Measures
