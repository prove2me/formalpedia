-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.BB.RatCoord.exists_algebraMap_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:10:43.52312+00:00
-- url     : https://prove2.me/submissions/9112f527-e236-4b56-97d6-f16bbdf44084

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateBijectionTraceForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB GlobalTheory.CompanionTheory.SW.BB.RatCoord
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
namespace GlobalTheory.CompanionTheory.SW.BB.RatCoord
theorem _root_.solution {F E : Type} [Field F] [Field E] [Algebra F E]
    (h2 : Module.finrank F E = 2) {σ : E →ₐ[F] E} (hne : σ ≠ AlgHom.id F E) {h : E}
    (hh : σ h = h) : ∃ c : F, h = algebraMap F E c := by
  by_contra hcon
  push Not at hcon
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have li : LinearIndependent F ![(1 : E), h] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      by_contra ht
      apply hcon (-(s / t))
      have h1 : algebraMap F E t * h = -algebraMap F E s := by
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
        linear_combination hst
      have ht' : algebraMap F E t ≠ 0 := by simpa using ht
      rw [map_neg, map_div₀]
      field_simp
      linear_combination h1
    subst ht
    simpa using hst
  have hspan : Submodule.span F (Set.range ![(1 : E), h]) = ⊤ :=
    li.span_eq_top_of_card_eq_finrank' (by simp [h2])
  apply hne
  have hlin : σ.toLinearMap = LinearMap.id := by
    apply LinearMap.ext_on_range hspan
    intro i
    fin_cases i
    · simp
    · simpa using hh
  ext y
  exact congrArg (fun f : E →ₗ[F] E => f y) hlin
end GlobalTheory.CompanionTheory.SW.BB.RatCoord
