-- Prove2me | solution 1 for GlobalTheory.DatumCoverAdjoint.span_image_sup_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:12:38.510847+00:00
-- url     : https://prove2.me/submissions/5da4e107-7020-409a-a03f-7c83a0d27c75

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsLevMove
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsQuotEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_LevelCoverDatumSimilitudeAdjointTransport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.DatumCoverAdjoint
open GlobalTheory.DatumInverseCharacter
namespace GlobalTheory.DatumCoverAdjoint
theorem _root_.solution {R M J : Type} [CommRing R] [AddCommGroup M] [Module R M] (K : Ideal R)
    (φ : M →ₗ[R] M) (hφ : ∀ a, ∃ b, φ b - a ∈ (K • ⊤ : Submodule R M)) (x : J → M) (s : Set J)
    (h : Submodule.span R (x '' s) ⊔ (K • ⊤ : Submodule R M) = ⊤) :
    Submodule.span R ((fun i => φ (x i)) '' s) ⊔ (K • ⊤ : Submodule R M) = ⊤ := by
  rw [eq_top_iff]
  intro a _
  obtain ⟨b, hb⟩ := hφ a
  have h1 : φ b ∈ Submodule.map φ (Submodule.span R (x '' s) ⊔ (K • ⊤ : Submodule R M)) :=
    Submodule.mem_map_of_mem (by rw [h]; exact Submodule.mem_top)
  rw [Submodule.map_sup, Submodule.map_span, Set.image_image, Submodule.map_smul''] at h1
  have h2 : φ b ∈ Submodule.span R ((fun i => φ (x i)) '' s) ⊔ (K • ⊤ : Submodule R M) :=
    SetLike.le_def.1 (sup_le_sup le_rfl (Submodule.smul_mono le_rfl le_top)) h1
  have := sub_mem h2 (Submodule.mem_sup_right hb)
  rwa [sub_sub_cancel] at this
end GlobalTheory.DatumCoverAdjoint
