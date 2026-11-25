-- Prove2me | solution 1 for GlobalTheory.CommonDenominator.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:42:26.962174+00:00
-- url     : https://prove2.me/submissions/5b151451-43fa-465e-ab6c-f7b3138d41c6

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AlgebraMapMemO
import Theorems.Thm_GlobalTheory_CommonDenominator_algebraMap_mem_O
import Theorems.Thm_GlobalTheory_CommonDenominator_exists_den
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
open ValuativeRel
open GlobalTheory GlobalTheory.CommonDenominator
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.CommonDenominator
theorem _root_.solution (L : Formalism.MainNotions.S.Loc.LocE F E) {n : ℕ} [IsNonarchimedeanLocalField F]
    {Λ : Submodule (↥(Formalism.MainNotions.S.Loc.LocE.O L)) (Fin n → E)} (hΛ : GlobalTheory.HL.IsLat L Λ)
    (x : Fin n → E) :
    ∃ (t : ↥(Valuation.integer (ValuativeRel.valuation F))),
      t ≠ (0 : ↥(Valuation.integer (ValuativeRel.valuation F))) ∧
      (Algebra.algebraMap F E : F → E) (↑t : F) • x ∈ Λ := by
  have hx : x ∈ Submodule.span E (Λ : Set (Fin n → E)) := by rw [hΛ.2]; exact Submodule.mem_top
  have key : ∀ (a : E) (ha : a ∈ L.O) (v : Fin n → E), v ∈ Λ → a • v ∈ Λ := by
    intro a ha v hv
    have := Λ.smul_mem (⟨a, ha⟩ : L.O) hv
    exact this
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simpa using Λ.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨t1, h1, hy⟩ := hy
    obtain ⟨t2, h2, hz⟩ := hz
    refine ⟨t1 * t2, mul_ne_zero h1 h2, ?_⟩
    have e : (Algebra.algebraMap F E : F → E) ((t1 * t2 : 𝒪[F]) : F) • (y + z)
        = algebraMap F E (t2 : F) • (algebraMap F E (t1 : F) • y)
          + algebraMap F E (t1 : F) • (algebraMap F E (t2 : F) • z) := by
      simp only [Subring.coe_mul, map_mul, smul_add, smul_smul]
      rw [mul_comm (algebraMap F E (t2 : F)) (algebraMap F E (t1 : F))]
    rw [e]
    exact Λ.add_mem (key _ (algebraMap_mem_O L t2) _ hy) (key _ (algebraMap_mem_O L t1) _ hz)
  | smul c y _ hy =>
    obtain ⟨t, ht, hy⟩ := hy
    obtain ⟨s, hs, hsc⟩ := exists_den L c
    refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
    have e : (Algebra.algebraMap F E : F → E) ((s * t : 𝒪[F]) : F) • (c • y)
        = (algebraMap F E (s : F) * c) • (algebraMap F E (t : F) • y) := by
      simp only [Subring.coe_mul, map_mul, smul_smul]
      rw [mul_right_comm]
    rw [e]
    exact key _ hsc _ hy
end GlobalTheory.CommonDenominator
