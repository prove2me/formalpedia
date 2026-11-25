-- Prove2me | solution 1 for GlobalTheory.PowMulMemOrder.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:06:14.54769+00:00
-- url     : https://prove2.me/submissions/8ce320ec-2272-4fc2-bb68-4d6ac3d13d8b

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsBisFurther
import Theorems.Thm_GlobalTheory_PowMulMemOrder_exists_pow_mul_mem
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
open GlobalTheory GlobalTheory.PowMulMemOrder
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.PowMulMemOrder
theorem _root_.solution : ∀ {F : Type} [inst : Field F] [inst_1 : ValuativeRel F] [inst_2 : TopologicalSpace F] [IsNonarchimedeanLocalField F] {E : Type} [inst_4 : CommRing E] [inst_5 : Algebra F E] [inst_6 : TopologicalSpace E] (L : Formalism.MainNotions.S.Loc.LocE F E) {ϖ : ↥(Valuation.integer (ValuativeRel.valuation F))}, Irreducible ϖ → ∀ (p : ↥(Formalism.MainNotions.S.Loc.LocE.O L)), (↑p : E) = (Algebra.algebraMap F E : F → E) (↑ϖ : F) → ∀ {n : ℕ} {Λ : Submodule (↥(Formalism.MainNotions.S.Loc.LocE.O L)) (Fin n → E)}, GlobalTheory.HL.IsLat L Λ → ∀ (v : Fin n → E), ∃ (j : ℕ), p ^ j • v ∈ Λ := by
  intro F _ _ _ _ E _ _ _ L ϖ hϖ p hp n Λ hΛ v
  have key : ∀ c : E, ∃ k : ℕ, ((p ^ k : L.O) : E) * c ∈ L.O := by
    intro c
    obtain ⟨k, hk⟩ := exists_pow_mul_mem L hϖ c
    refine ⟨k, ?_⟩
    have : ((p ^ k : L.O) : E) = algebraMap F E ((ϖ : F) ^ k) := by
      rw [SubmonoidClass.coe_pow, hp, map_pow]
    rw [this]; exact hk
  have mono : ∀ (x : Fin n → E) (i j : ℕ), p ^ j • x ∈ Λ → p ^ (i + j) • x ∈ Λ := by
    intro x i j h
    rw [pow_add, mul_smul]
    exact Λ.smul_mem _ h
  have hv : v ∈ Submodule.span E (Λ : Set (Fin n → E)) := by rw [hΛ.2]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, by simpa using hx⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    rw [smul_add]
    refine Λ.add_mem ?_ (mono y a b hb)
    rw [add_comm]; exact mono x b a ha
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨k, hk⟩ := key c
    refine ⟨k + a, ?_⟩
    have e1 : p ^ (k + a) • (c • x) = (⟨((p ^ k : L.O) : E) * c, hk⟩ : L.O) • (p ^ a • x) := by
      simp only [Subring.smul_def, smul_smul, pow_add, Subring.coe_mul]
      congr 1
      ring
    rw [e1]
    exact Λ.smul_mem _ ha
end GlobalTheory.PowMulMemOrder
