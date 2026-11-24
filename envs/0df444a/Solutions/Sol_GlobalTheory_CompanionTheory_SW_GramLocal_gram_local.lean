-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GramLocal.gram_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:15:44.874013+00:00
-- url     : https://prove2.me/submissions/e2ce63aa-c313-4d96-94aa-4f66081b66f6

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramMatrixLocalGlobal
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramLocal_bcE_inclR
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramLocal_bcE_gramR
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramLocal_gramR_ratTup
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramLocal_tensor_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GramLocal
namespace GlobalTheory.CompanionTheory.SW.GramLocal
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (X : (Fin n → Fin M → AF F ⊗[F] E)) (T : Matrix (Fin n) (Fin n) E), (gramR (AF F) σ J X = T.map (inclR (AF F)) ↔ gramR (Ainf F) σ J (projInf X) = T.map (inclR (Ainf F)) ∧ ∀ v, gramR (Fv F v) σ J (projV v (projFin X)) = T.map (inclR (Fv F v))) ∧ ∀ Y : Fin n → Fin M → E, gramR (AF F) σ J (ratTup (AF F) Y) = (gramE σ J Y).map (inclR (AF F)) := by
  intro F E _ _ _ _ _ σ hCM M J _ n X T
  have hfin : Module.Finite F E :=
    Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hInf : gramR (Ainf F) σ J (projInf X) =
      fun a b => bcE E (fstA F) (gramR (AF F) σ J X a b) := bcE_gramR (fstA F) σ J X
  have hFin : gramR (Af F) σ J (projFin X) =
      fun a b => bcE E (sndA F) (gramR (AF F) σ J X a b) := bcE_gramR (sndA F) σ J X
  have hV : ∀ v, gramR (Fv F v) σ J (projV v (projFin X)) =
      fun a b => bcE E (evalV F v) (bcE E (sndA F) (gramR (AF F) σ J X a b)) := by
    intro v
    have := bcE_gramR (evalV F v) σ J (projFin X : Fin n → Fin M → Af F ⊗[F] E)
    rw [hFin] at this
    exact this
  refine ⟨⟨fun h => ⟨?_, fun v => ?_⟩, fun h => ?_⟩, fun Y => gramR_ratTup σ J Y⟩
  · rw [hInf, h]
    funext a b
    simp only [Matrix.map_apply, bcE_inclR]
  · rw [hV v, h]
    funext a b
    simp only [Matrix.map_apply, bcE_inclR]
  · funext a b
    apply tensor_ext
    · have := congrFun (congrFun (hInf.symm.trans h.1) a) b
      simpa only [Matrix.map_apply, bcE_inclR] using this
    · intro v
      have := congrFun (congrFun ((hV v).symm.trans (h.2 v)) a) b
      simpa only [Matrix.map_apply, bcE_inclR] using this
end GlobalTheory.CompanionTheory.SW.GramLocal
