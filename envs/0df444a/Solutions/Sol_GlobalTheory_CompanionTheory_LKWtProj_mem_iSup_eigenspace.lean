-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LKWtProj.mem_iSup_eigenspace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:48:29.589596+00:00
-- url     : https://prove2.me/submissions/31864529-788c-4d9c-b67b-7a867d187cd3

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_WtProj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped InnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LKWtProj
open CompanionTheory.D.LK
open CompanionTheory.D.DSIC (KRel KUnit KStab)
namespace GlobalTheory.CompanionTheory.LKWtProj
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (T : Module.End ℂ V)
    (hT : T.IsSymmetric) (S : Submodule ℂ V) [FiniteDimensional ℂ S] (hS : ∀ v ∈ S, T v ∈ S) (x : V) (hx : x ∈ S) :
    x ∈ ⨆ μ : ℂ, T.eigenspace μ := by
  have hs : (T.restrict hS).IsSymmetric := hT.restrict_invariant hS
  have htop : (⨆ μ : ℂ, Module.End.eigenspace (T.restrict hS) μ) = ⊤ :=
    Submodule.orthogonal_eq_bot_iff.1 hs.orthogonalComplement_iSup_eigenspaces_eq_bot
  have hle : ((⨆ μ : ℂ, Module.End.eigenspace (T.restrict hS) μ).map S.subtype) ≤ ⨆ μ : ℂ, T.eigenspace μ := by
    rw [Submodule.map_iSup]
    refine iSup_mono fun μ => ?_
    rintro _ ⟨y, hy, rfl⟩
    have hy' := Module.End.mem_eigenspace_iff.1 hy
    rw [Module.End.mem_eigenspace_iff]
    exact congrArg Subtype.val hy'
  exact hle ⟨⟨x, hx⟩, by rw [htop]; trivial, rfl⟩
end GlobalTheory.CompanionTheory.LKWtProj
