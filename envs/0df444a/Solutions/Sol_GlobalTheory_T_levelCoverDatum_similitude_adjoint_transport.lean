-- Prove2me | solution 1 for GlobalTheory.T.levelCoverDatum_similitude_adjoint_transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:22:11.437661+00:00
-- url     : https://prove2.me/submissions/6df9b7b6-427c-4f34-9e58-b4769e1a1e0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_LevelCoverDatumSimilitudeAdjointTransport
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsLevMove
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_LevelCoverDatumSimilitudeAdjointTransportStatement
import Theorems.Thm_GlobalTheory_DatumCoverAdjoint_datum_adjoint


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.l₂.M = l.M * d.pd → d.l₂.Mb = l.Mb * d.I → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (x₀ : Fin n → LaJ Xo c d), d.PhiPin ph ψ x₀ → ∀ g : Sim Dw, (∀ a, g.f d.l₂.M a - a ∈ d.I • (⊤ : Submodule (𝓞 E) Dw.La)) → ∃ σq : LevQ Dw d.l₂ ≃ LevQ Dw d.l₂, (∀ a, σq (Submodule.Quotient.mk a) = Submodule.Quotient.mk (g.f d.l₂.M a)) ∧ ∀ (rk : Bool) (x0 : Fin n → Dw.La), AdmX (l := l) rk x0 → ∃ x0' : Fin n → Dw.La, AdmX (l := l) rk x0' ∧ ∀ q : Fin n → LevQ Dw d.l₂, d.w x0 (fun b => σq.symm (q b)) = d.w x0' q := by
  first | exact @GlobalTheory.DatumCoverAdjoint.datum_adjoint | exact GlobalTheory.DatumCoverAdjoint.datum_adjoint | (intros; apply GlobalTheory.DatumCoverAdjoint.datum_adjoint <;> assumption)
end _root_.GlobalTheory.T
