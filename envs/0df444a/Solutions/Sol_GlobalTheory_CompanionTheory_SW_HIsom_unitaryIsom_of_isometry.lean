-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HIsom.unitaryIsom_of_isometry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:01:33.735246+00:00
-- url     : https://prove2.me/submissions/203b7b15-0ab3-4c2e-9079-756d531e48e0

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitaryIsomOfIsometry
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HIsom_conj_mem_UJ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HIsom_conj_inv_mem_UJ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HIsom_JR_conj
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HIsom_isTopologicalRing_tens

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
open GlobalTheory.CompanionTheory.SW.HIsom
namespace GlobalTheory.CompanionTheory.SW.HIsom
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (g : GL (Fin M) E) (J' : Matrix (Fin M) (Fin M) E), J' = cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * g → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R], ∃ e : HA R σ J' ≃ₜ* HA R σ J, (∀ u, HA.mat R σ J (e u) = bc (inclR R) g * HA.mat R σ J' u * (bc (inclR R) g)⁻¹) ∧ ∀ u, HA.mat R σ J (e u) ∈ HFin R σ J ↔ HA.mat R σ J' u ∈ HFin R σ J' := by
  intro F E _ _ _ _ _ σ hCM M J _ g J' hJ' R _ _ _ _
  subst hJ'
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  haveI : IsTopologicalRing (R ⊗[F] E) := isTopologicalRing_tens F E R
  set G : GL (Fin M) (R ⊗[F] E) := bc (inclR R) g with hG
  have hJR := JR_conj R σ J g
  have h₁ : ∀ u ∈ HR R σ (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E)),
      G * u * G⁻¹ ∈ HR R σ J := by
    intro u hu
    refine conj_mem_UJ (sigR R σ) (JR R J) G u ?_
    have : u ∈ UJ (sigR R σ) (JR R (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E))) := hu
    rwa [hJR] at this
  have h₂ : ∀ u ∈ HR R σ J,
      G⁻¹ * u * G ∈ HR R σ (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E)) := by
    intro u hu
    change G⁻¹ * u * G ∈ UJ (sigR R σ) (JR R (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E)))
    rw [hJR]
    exact conj_inv_mem_UJ (sigR R σ) (JR R J) G u hu
  refine ⟨conjHomeo _ _ G h₁ h₂, fun u => rfl, fun u => ?_⟩
  change G * HA.mat R σ _ u * G⁻¹ ∈ HFin R σ J ↔ _
  constructor
  · rintro ⟨w, hw, hwu⟩
    refine ⟨g⁻¹ * w * g, conj_inv_mem_UJ (σ : E →+* E) J g w hw, ?_⟩
    have : bc (inclR R) w = G * HA.mat R σ _ u * G⁻¹ := hwu
    simp only [map_mul, map_inv, this, ← hG]
    group
  · rintro ⟨w, hw, hwu⟩
    refine ⟨g * w * g⁻¹, conj_mem_UJ (σ : E →+* E) J g w hw, ?_⟩
    have : bc (inclR R) w = HA.mat R σ _ u := hwu
    simp only [map_mul, map_inv, this, ← hG]
end GlobalTheory.CompanionTheory.SW.HIsom
