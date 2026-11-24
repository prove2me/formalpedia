-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.TopH.topH_props
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:12:42.408319+00:00
-- url     : https://prove2.me/submissions/a59d46a9-6583-4b82-8110-970ab177dbf7

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupLocallyCompact
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_TopH_hform_mulVec
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_TopH_isClosed_HR
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_TopK_topTens_props


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.TopH
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
namespace GlobalTheory.CompanionTheory.SW.TopH
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R], IsTopologicalGroup (HA R σ J) ∧ LocallyCompactSpace (HA R σ J) ∧ SecondCountableTopology (HA R σ J) ∧ T2Space (HA R σ J) ∧ BorelSpace (HA R σ J) ∧ ∀ n : ℕ, (Continuous fun p : HA R σ J × (Fin n → Fin M → R ⊗[F] E) => actW R σ J p.1 p.2) ∧ (∀ X : Fin n → Fin M → R ⊗[F] E, actW R σ J 1 X = X) ∧ (∀ (g h : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E), actW R σ J (g * h) X = actW R σ J g (actW R σ J h X)) ∧ ∀ (h : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E), gramR R σ J (actW R σ J h X) = gramR R σ J X := by
  intro F E _ _ _ _ _ σ hCM M J _ R _ _ _ _ _ _ _
  obtain ⟨h1, h2, h3, h4, hs, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM R
  haveI := h1; haveI := h2; haveI := h3; haveI := h4
  haveI : LocallyCompactSpace (Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin M → Fin M → R ⊗[F] E))
  haveI : SecondCountableTopology (Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin M → Fin M → R ⊗[F] E))
  haveI : T2Space (Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin M → Fin M → R ⊗[F] E))
  haveI : LocallyCompactSpace (Matrix (Fin M) (Fin M) (R ⊗[F] E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isOpenEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Matrix (Fin M) (Fin M) (R ⊗[F] E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : LocallyCompactSpace (GL (Fin M) (R ⊗[F] E)) :=
    Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (GL (Fin M) (R ⊗[F] E)) :=
    Units.isEmbedding_embedProduct.isInducing.secondCountableTopology
  have hcl := isClosed_HR R σ hs J
  haveI g1 : IsTopologicalGroup (HR R σ J) := inferInstance
  haveI g2 : LocallyCompactSpace (HR R σ J) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI g3 : SecondCountableTopology (HR R σ J) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI g4 : T2Space (HR R σ J) := inferInstance
  refine ⟨g1, g2, g3, g4, ⟨rfl⟩, fun n => ⟨?_, ?_, ?_, ?_⟩⟩
  · have hm : Continuous fun p : HA R σ J × (Fin n → Fin M → R ⊗[F] E) =>
        ((HA.mat R σ J p.1 : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
      Units.continuous_val.comp (continuous_subtype_val.comp continuous_fst)
    exact continuous_pi fun a => hm.matrix_mulVec ((continuous_apply a).comp continuous_snd)
  · intro X
    funext a
    exact Matrix.one_mulVec (X a)
  · intro g h X
    funext a
    change ((HA.mat R σ J g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * (HA.mat R σ J h : Matrix (Fin M) (Fin M) _)) *ᵥ X a = _
    exact (Matrix.mulVec_mulVec _ _ _).symm
  · intro h X
    funext a b
    exact hform_mulVec (sigR R σ) (JR R J) _ h.2 (X a) (X b)
end GlobalTheory.CompanionTheory.SW.TopH
