-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.BB.InfDens.e_half_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:10:48.742156+00:00
-- url     : https://prove2.me/submissions/1a31e8c1-0b44-4e20-aa5d-9674a810a077

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanCoordinateMeasureTransportStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHomeomorphRankOneTuplesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianRankOneHomeomorphBase
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyRealStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanLocalDensityFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB GlobalTheory.CompanionTheory.SW.BB.InfDens
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.BB.InfDens
theorem _root_.solution {σ : E →ₐ[F] E} {M d : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F)
    (hB : ∀ x y : Fin M → Ainf F ⊗[F] E,
      Algebra.trace (Ainf F) (Ainf F ⊗[F] E) (hR (Ainf F) σ J x y) =
        cv (Ainf F) b x ⬝ᵥ (B.map (algebraMap F (Ainf F)) *ᵥ cv (Ainf F) b y))
    (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ))
    (hρ : ∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x)
    (X : Fin 1 → Fin M → Ainf F ⊗[F] E) (w : InfinitePlace F) :
    e (algebraMap F (Ainf F) (1 / 2) *
        Algebra.trace (Ainf F) (Ainf F ⊗[F] E) (gramR (Ainf F) σ J X 0 0)) w =
      (1 / 2 : ℝ) * (xw e b X w ⬝ᵥ (B.map (ρ w) *ᵥ xw e b X w)) := by
  let ew : Ainf F →+* ℝ := (Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) w).comp (e : Ainf F →+* _)
  have hew : ∀ a, ew a = e a w := fun _ => rfl
  have hcomp : ew.comp (algebraMap F (Ainf F)) = ρ w := RingHom.ext fun x => hρ x w
  have hx : xw e b X w = ew ∘ cv (Ainf F) b (X 0) := rfl
  have hm : B.map (ρ w) = (B.map (algebraMap F (Ainf F))).map ew := by
    rw [← hcomp]
    ext i j
    rfl
  have hhalf : ρ w (1 / 2) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
  rw [← hew, map_mul, hew, hρ, hhalf]
  show _ * ew (Algebra.trace (Ainf F) (Ainf F ⊗[F] E) (hR (Ainf F) σ J (X 0) (X 0))) = _
  rw [hB, hx, hm, RingHom.map_dotProduct]
  have hv : ⇑ew ∘ (B.map (algebraMap F (Ainf F)) *ᵥ cv (Ainf F) b (X 0)) =
      (B.map (algebraMap F (Ainf F))).map ew *ᵥ (⇑ew ∘ cv (Ainf F) b (X 0)) :=
    funext fun i => RingHom.map_mulVec ew _ _ i
  rw [hv]
end GlobalTheory.CompanionTheory.SW.BB.InfDens
