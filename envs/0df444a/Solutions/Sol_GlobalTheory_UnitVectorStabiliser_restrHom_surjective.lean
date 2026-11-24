-- Prove2me | solution 1 for GlobalTheory.UnitVectorStabiliser.restrHom_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:25:57.717925+00:00
-- url     : https://prove2.me/submissions/3d29cd7f-b7c4-40a1-8008-39a154bc1d6f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RestrHomSurjective
import Theorems.Thm_GlobalTheory_UnitVectorStabiliser_exists_extend
import Theorems.Thm_GlobalTheory_SelfDualLatticeCompare_sigR_sigR


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal
open GlobalTheory GlobalTheory.UnitVectorStabiliser
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F))
namespace GlobalTheory.UnitVectorStabiliser
theorem _root_.solution (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    (L : Submodule (OEv F E v) (Fin M → Ev F E v)) (x : Fin M → Ev F E v)
    (hx : IsUnit (hR (Fv F v) σ J x x)) :
    Function.Surjective (restrHom σ J v (perpLat σ J v L x) x) := by
  rintro ⟨u, hu, hu'⟩
  have hJ' : ∀ i j, sigR (Fv F v) σ (JR (Fv F v) J j i) = JR (Fv F v) J i j := by
    intro i j
    show (1 : Fv F v) ⊗ₜ[F] σ (J j i) = (1 : Fv F v) ⊗ₜ[F] J i j
    rw [hJ.1]
  have hd : IsUnit (JR (F := F) (Fv F v) J).det := by
    have := (RingHom.map_det (inclR (F := F) (Fv F v)) J)
    rw [show JR (F := F) (Fv F v) J = (inclR (F := F) (Fv F v)).mapMatrix J from rfl, ← this]
    exact (hJ.2.isUnit).map _
  obtain ⟨g, hg, hgx, hgu⟩ := exists_extend _ _
    (GlobalTheory.SelfDualLatticeCompare.sigR_sigR (Fv F v) h) hJ' hd x hx (perp σ J v x)
    (fun _ => Iff.rfl) u.toLinearMap hu
  let g' : HA (Fv F v) σ J := (⟨g, hg⟩ : HR (Fv F v) σ J)
  have hv : g' ∈ stabVec σ J v x := (mem_stabVec σ J v x g').2 hgx
  have hgu' : ∀ y : perp σ J v x, act σ J v g' y = u y := hgu
  have hl : g' ∈ stabLat σ J v (perpLat σ J v L x) := by
    show ∀ y, y ∈ perpLat σ J v L x ↔ act σ J v g' y ∈ perpLat σ J v L x
    intro y
    by_cases hy : y ∈ perp σ J v x
    · rw [hgu' ⟨y, hy⟩]
      exact hu' ⟨y, hy⟩
    · exact ⟨fun h => (hy h.1).elim,
        fun h => (hy ((act_mem_perp_iff σ J v x g' hv y).1 h.1)).elim⟩
  exact ⟨⟨g', hl, hv⟩, Subtype.ext (LinearEquiv.ext fun y => Subtype.ext (hgu' y))⟩
end GlobalTheory.UnitVectorStabiliser
