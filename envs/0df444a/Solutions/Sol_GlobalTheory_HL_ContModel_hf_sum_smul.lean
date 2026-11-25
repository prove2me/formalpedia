-- Prove2me | solution 1 for GlobalTheory.HL.ContModel.hf_sum_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:45:34.529798+00:00
-- url     : https://prove2.me/submissions/39a36983-70ff-4eb6-b9f8-959b24559d95

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NcardImageOfLe
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
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.ContModel
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.ContModel
theorem _root_.solution (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x : Fin m → Fin n → E)
    (c d : Fin m → E) :
    hf L Hm (∑ i, c i • x i) (∑ k, d k • x k) = ∑ i, ∑ k, L.cj (d k) * hf L Hm (x i) (x k) * c i := by
  simp only [hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul,
    Finset.mul_sum]
  calc _ = ∑ a, ∑ b, ∑ i, ∑ k, c i * x i a * Hm a b * (L.cj (d k) * L.cj (x k b)) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        first | rfl | exact Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ b, ∑ k, c i * x i a * Hm a b * (L.cj (d k) * L.cj (x k b)) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i, ∑ a, ∑ b, ∑ k, c i * x i a * Hm a b * (L.cj (d k) * L.cj (x k b)) := Finset.sum_comm
    _ = ∑ i, ∑ a, ∑ k, ∑ b, c i * x i a * Hm a b * (L.cj (d k) * L.cj (x k b)) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ i, ∑ k, ∑ a, ∑ b, c i * x i a * Hm a b * (L.cj (d k) * L.cj (x k b)) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ =>
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
end GlobalTheory.HL.ContModel
