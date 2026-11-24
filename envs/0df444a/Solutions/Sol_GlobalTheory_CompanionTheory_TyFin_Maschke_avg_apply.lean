-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.Maschke.avg_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:51.155192+00:00
-- url     : https://prove2.me/submissions/9fcea4c7-11b9-4090-bc44-05a3cdf8c31f

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MaschkeProperties

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.Maschke
variable {Γ : Type} [Group Γ] [Fintype Γ]
variable {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]
namespace GlobalTheory.CompanionTheory.TyFin.Maschke
theorem _root_.solution (ρ : Representation ℂ Γ V) (σ : Representation ℂ Γ W) (f : V →ₗ[ℂ] W) (v : V) :
    avg ρ σ f v = (Fintype.card Γ : ℂ)⁻¹ • ∑ g : Γ, σ g (f (ρ g⁻¹ v)) := by
  simp [avg, LinearMap.sum_apply]
end GlobalTheory.CompanionTheory.TyFin.Maschke
