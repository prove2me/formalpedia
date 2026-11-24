-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.BB.RatCoord.coords_ratTup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:49:18.362946+00:00
-- url     : https://prove2.me/submissions/4434acaf-9e87-41c5-84b7-21524cddf433

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsTraceFormGramMatrixInBasis
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteComponentCoordinatesAction
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BB_RatCoord_repr_map
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BB_RatCoord_cv_act

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB GlobalTheory.CompanionTheory.SW.BB.RatCoord
namespace GlobalTheory.CompanionTheory.SW.BB.RatCoord
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → ∀ (ω : HA (AF F) σ J) (x : Fin M × Fin d → F), (∀ w, xw e b (projInf (actW (AF F) σ J ω⁻¹ (ratTup (AF F) (ofF b x)))) w = ginf e σ J b ω w *ᵥ fun j => ρ w (x j)) ∧ cv (Af F) b (projFin (actW (AF F) σ J ω⁻¹ (ratTup (AF F) (ofF b x))) 0) = gfin σ J b ω *ᵥ fun j => algebraMap F (Af F) (x j) := by
  intro F E _ _ _ _ _ σ _ M J _ d b ρ e he ω x
  have hY := cv_act (AF F) σ J b ω⁻¹ x
  set Y := actW (AF F) σ J ω⁻¹ (ratTup (AF F) (ofF b x)) with hYdef
  have hc : ∀ p, (Algebra.TensorProduct.basis (AF F) b).repr (Y 0 p.1) p.2 =
      (gmat (AF F) σ J b ω⁻¹ *ᵥ fun j => algebraMap F (AF F) (x j)) p := fun p =>
    congrFun hY p
  refine ⟨fun w => ?_, ?_⟩
  · funext p
    let φ : AF F →+* ℝ :=
      (Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) w).comp
        ((e : Ainf F →+* (InfinitePlace F → ℝ)).comp (fstA F : AF F →+* Ainf F))
    have h1 : xw e b (projInf Y) w p = φ ((Algebra.TensorProduct.basis (AF F) b).repr (Y 0 p.1) p.2) := by
      change e ((Algebra.TensorProduct.basis (Ainf F) b).repr
        (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (Y 0 p.1)) p.2) w = _
      rw [repr_map]
      rfl
    rw [h1, hc, RingHom.map_mulVec]
    have h2 : (φ ∘ fun j => algebraMap F (AF F) (x j)) = fun j => ρ w (x j) := by
      funext j
      change e (fstA F (algebraMap F (AF F) (x j))) w = _
      rw [(fstA F).commutes, he]
    rw [h2]
    rfl
  · funext p
    have h1 : cv (Af F) b (projFin Y 0) p =
        (sndA F : AF F →+* Af F) ((Algebra.TensorProduct.basis (AF F) b).repr (Y 0 p.1) p.2) := by
      change (Algebra.TensorProduct.basis (Af F) b).repr
        (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (Y 0 p.1)) p.2 = _
      rw [repr_map]
      rfl
    rw [h1, hc, RingHom.map_mulVec]
    have h2 : ((sndA F : AF F →+* Af F) ∘ fun j => algebraMap F (AF F) (x j)) =
        fun j => algebraMap F (Af F) (x j) := by
      funext j
      exact (sndA F).commutes (x j)
    rw [h2]
    rfl
end GlobalTheory.CompanionTheory.SW.BB.RatCoord
