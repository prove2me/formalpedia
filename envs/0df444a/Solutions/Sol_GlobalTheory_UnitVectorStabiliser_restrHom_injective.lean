-- Prove2me | solution 1 for GlobalTheory.UnitVectorStabiliser.restrHom_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:05:17.656+00:00
-- url     : https://prove2.me/submissions/dfdedf5d-5f08-46e7-a08a-8a0c310ba3e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RestrHomSurjective
import Theorems.Thm_GlobalTheory_UnitVectorStabiliser_exists_proj

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
theorem _root_.solution (L' : Submodule (OEv F E v) (Fin M → Ev F E v)) (x : Fin M → Ev F E v)
    (hx : IsUnit (hR (Fv F v) σ J x x)) : Function.Injective (restrHom σ J v L' x) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨c, p, h1, -, -⟩ := exists_proj _ _ x hx (perp σ J v x) (fun _ => Iff.rfl)
  have h0 : ∀ y : perp σ J v x, act σ J v g y = y := fun y =>
    congrArg (fun u : unitaryLatIn σ J v (perp σ J v x) L' =>
      ((u.1 y : perp σ J v x) : Fin M → Ev F E v)) hg
  have hx' := (mem_stabVec σ J v x g).1 g.2.2
  have h2 : ∀ y, act σ J v g y = y := by
    intro y
    rw [h1 y]
    have := h0 (p y)
    unfold act at *
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hx', this]
  refine Subtype.ext (Subtype.ext (Units.ext ?_))
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun y => ?_
  exact (h2 y).trans (act_one σ J v y).symm
end GlobalTheory.UnitVectorStabiliser
