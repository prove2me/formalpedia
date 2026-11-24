-- Prove2me | solution 1 for GlobalTheory.SelfDualLatticeCompare.unitVectors_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:36:06.524572+00:00
-- url     : https://prove2.me/submissions/d7a8f91c-1128-4c9e-b3ae-23dd6cb231f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_UnitaryLatticeOrthogonal
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_SelfDualLatticeActions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Theorems.Thm_GlobalTheory_SelfDualLatticeCompare_disjoint_span_perpLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory GlobalTheory.SelfDualLatticeCompare
open GlobalTheory.IndefiniteRowSideFullHecke
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F))
namespace GlobalTheory.SelfDualLatticeCompare
theorem _root_.solution (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    (L : Submodule (SelfDualLatticeActions.OEv E v) (SelfDualLatticeActions.Wv E v M)) (β : Fv F v) (hβ : IsUnit β) :
    UnitaryLatticeOrthogonal.UnitVectors σ J v L β ↔ SelfDualLatticeActions.UnitVectorClaims v σ J L β := by
  refine and_congr Iff.rfl (and_congr ?_ Iff.rfl)
  refine forall_congr' fun x => forall_congr' fun hx => ?_
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1.symm, disjoint_span_perpLat σ J v h hJ L x (hx.2 ▸ hβ), h2⟩
  · rintro ⟨h1, -, h2⟩
    exact ⟨h1.symm, h2⟩
end GlobalTheory.SelfDualLatticeCompare
