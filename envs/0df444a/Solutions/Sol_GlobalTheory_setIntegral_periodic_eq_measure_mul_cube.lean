-- Prove2me | solution 1 for GlobalTheory.setIntegral_periodic_eq_measure_mul_cube
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:32:42.946679+00:00
-- url     : https://prove2.me/submissions/e1d7b855-9252-4ece-9361-69ffe2d8d274

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SetIntegralPeriodLatticeEqVolumeMulCube

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {E I : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I]
    (ν : Measure E) [ν.IsAddHaarMeasure] (T : (I → ℝ) ≃L[ℝ] E) (Λ : Submodule ℤ E)
    (hΛ : ∀ p, T p ∈ Λ ↔ ∀ i, ∃ k : ℤ, (k : ℝ) = p i)
    (Fd : Set E) (hFd : IsAddFundamentalDomain Λ Fd ν)
    (F : E → ℝ) (hF : ∀ (l : Λ) z, F (z + l) = F z) :
    ∫ z in Fd, F z ∂ν = (ν Fd).toReal *
      ∫ p in Set.pi Set.univ (fun _ : I => Set.Ico (0 : ℝ) 1), F (T p) := by
  classical
  set b : Module.Basis I ℝ E := (Pi.basisFun ℝ I).map T.toLinearEquiv with hb
  have hrepr : ∀ p i, b.repr (T p) i = p i := by
    intro p i
    simp [hb]
  have hspan : Λ = Submodule.span ℤ (Set.range b) := by
    ext z
    obtain ⟨p, rfl⟩ := T.surjective z
    rw [hΛ, Module.Basis.mem_span_iff_repr_mem]
    simp [hrepr]
  subst hspan
  have hcell := ZSpan.isAddFundamentalDomain b ν
  have hpre : T ⁻¹' ZSpan.fundamentalDomain b
      = Set.pi Set.univ (fun _ : I => Set.Ico (0 : ℝ) 1) := by
    ext p
    simp only [Set.mem_preimage, ZSpan.mem_fundamentalDomain, hrepr, Set.mem_pi, Set.mem_univ,
      true_imp_iff]
  have hcount : Countable (Submodule.span ℤ (Set.range b)) := inferInstance
  haveI : VAddInvariantMeasure (Submodule.span ℤ (Set.range b)) E ν :=
    ⟨fun c s _ => measure_preimage_add ν (c : E) s⟩
  have h1 : ∫ z in Fd, F z ∂ν = ∫ z in ZSpan.fundamentalDomain b, F z ∂ν :=
    hFd.setIntegral_eq hcell (fun l z => by
      have := hF l z
      rw [add_comm] at this
      exact this)
  have h2 : ν Fd = ν (ZSpan.fundamentalDomain b) := hFd.measure_eq hcell
  let e : (I → ℝ) ≃ᵐ E := T.toHomeomorph.toMeasurableEquiv
  have he : (e : (I → ℝ) → E) = T := rfl
  haveI : (Measure.map T (volume : Measure (I → ℝ))).IsAddHaarMeasure :=
    T.isAddHaarMeasure_map _
  obtain ⟨c, hc⟩ : ∃ c : NNReal, ν = c • Measure.map e (volume : Measure (I → ℝ)) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul ν (Measure.map T volume)⟩
  have h3 : ν (ZSpan.fundamentalDomain b) = c := by
    rw [hc, Measure.smul_apply, e.map_apply, he, hpre, Real.volume_pi_Ico]
    simp
  rw [h1, h2, h3, hc, Measure.restrict_smul, integral_smul_nnreal_measure, setIntegral_map_equiv,
    he, hpre]
  simp [NNReal.smul_def]
end GlobalTheory
