-- Prove2me | solution 1 for GlobalTheory.HL.QReflGen.induct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:24:22.728625+00:00
-- url     : https://prove2.me/submissions/19125007-a88b-455a-bc09-44b51334024b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfPerpEqBot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsometriesFixingSubspaceLeQuasiReflectionClosure
import Theorems.Thm_GlobalTheory_HL_QReflGen_hf_add_r
import Theorems.Thm_GlobalTheory_HL_QReflGen_hf_smul_r
import Theorems.Thm_GlobalTheory_HL_QReflGen_hf_cj
import Theorems.Thm_GlobalTheory_HL_QReflGen_step
import Theorems.Thm_GlobalTheory_HL_QReflGen_qrefl_fix
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.QReflGen
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.QReflGen
theorem _root_.solution [CharZero F] (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm)
    (Y : Submodule E (Fin n → E)) (hY : Y ⊔ perp L Hm Y = ⊤) {d : ℕ} (w : Fin d → Fin n → E)
    (hw : Submodule.span E (Set.range w) = perp L Hm Y) (hu : ∀ i, IsUnit (hf L Hm (w i) (w i)))
    (ho : ∀ i j, i ≠ j → hf L Hm (w i) (w j) = 0) (S : Finset (Fin d)) :
    ∀ g ∈ isomG L Hm, (∀ v ∈ Y, g v = v) → (∀ j, j ∉ S → g (w j) = w j) →
      g ∈ Subgroup.closure {g | ∃ a ∈ perp L Hm Y, IsQRefl L Hm a g} := by
  induction S using Finset.induction_on with
  | empty =>
    intro g _ h1 h2
    have : g = 1 := by
      apply LinearEquiv.toLinearMap_injective
      have hle : (⊤ : Submodule E (Fin n → E)) ≤
          LinearMap.eqLocus g.toLinearMap (1 : (Fin n → E) ≃ₗ[E] (Fin n → E)).toLinearMap := by
        rw [← hY, ← hw, sup_le_iff, Submodule.span_le]
        refine ⟨fun v hv => h1 v hv, ?_⟩
        rintro _ ⟨j, rfl⟩
        exact h2 j (by simp)
      exact LinearMap.ext fun v => hle (Submodule.mem_top (x := v))
    rw [this]; exact one_mem _
  | insert i S hi ih =>
    intro g hg h1 h2
    have hwp : w i ∈ perp L Hm Y := hw ▸ Submodule.subset_span ⟨i, rfl⟩
    have hyp : g (w i) ∈ perp L Hm Y := fun z hz => by
      rw [← h1 z hz, hg (w i) z]; exact hwp z hz
    obtain ⟨u, σ, ρ, hσ, hρ, hσρ⟩ := step L h (w i) (g (w i)) (hu i) (hg _ _)
    have hap : w i + (-u) • g (w i) ∈ perp L Hm Y := add_mem hwp (Submodule.smul_mem _ _ hyp)
    have mσ : σ ∈ Subgroup.closure {g | ∃ a ∈ perp L Hm Y, IsQRefl L Hm a g} :=
      Subgroup.subset_closure ⟨_, hap, hσ⟩
    have mρ : ρ ∈ Subgroup.closure {g | ∃ a ∈ perp L Hm Y, IsQRefl L Hm a g} :=
      Subgroup.subset_closure ⟨_, hyp, hρ⟩
    have key : ∀ v, σ v = ρ (g v) → (σ⁻¹ * ρ * g) v = v := fun v hv => by
      change σ.symm (ρ (g v)) = v
      rw [← hv, LinearEquiv.symm_apply_apply]
    have hg' := ih (σ⁻¹ * ρ * g) (mul_mem (mul_mem (inv_mem hσ.2.1) hρ.2.1) hg)
      (fun v hv => key v (by
        rw [h1 v hv, qrefl_fix L hσ (by rw [← hf_cj L h, hap v hv, map_zero]),
          qrefl_fix L hρ (by rw [← hf_cj L h, hyp v hv, map_zero])]))
      (fun j hj => key _ (by
        by_cases hji : j = i
        · rw [hji]; exact hσρ
        · have hj2 := h2 j (by simp [hji, hj])
          have h3 : hf L Hm (w j) (g (w i)) = 0 := by
            rw [← hj2, hg (w j) (w i)]; exact ho j i hji
          rw [hj2, qrefl_fix L hσ (by rw [hf_add_r, hf_smul_r, h3, ho j i hji]; simp),
            qrefl_fix L hρ h3]))
    have : g = ρ⁻¹ * σ * (σ⁻¹ * ρ * g) := by group
    rw [this]
    exact mul_mem (mul_mem (inv_mem mρ) mσ) hg'
end GlobalTheory.HL.QReflGen
