-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.asAlgebraHom_centralIdem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:47:34.781979+00:00
-- url     : https://prove2.me/submissions/2531b412-13c5-419e-9c58-50dcdce9912c

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCentralIdempotent
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CentralIdempotentAction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin
namespace GlobalTheory.CompanionTheory.TyFin
theorem _root_.solution {Γ V W : Type} [Group Γ] [Fintype Γ] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ Γ V) (σ : Representation ℂ Γ W) :
    σ.asAlgebraHom (centralIdem ρ) =
      ∑ g, ((Module.finrank ℂ V : ℂ) / Fintype.card Γ * LinearMap.trace ℂ V (ρ g⁻¹)) • σ g := by
  unfold centralIdem
  rw [map_sum]
  exact Finset.sum_congr rfl fun g _ => Representation.asAlgebraHom_single _ _ _
end GlobalTheory.CompanionTheory.TyFin
