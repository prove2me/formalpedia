-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.StandardFourierShortSpan.StdFourier.unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:55:18.709768+00:00
-- url     : https://prove2.me/submissions/d67ae3ad-dfe4-450b-973a-72c5c7ca3275

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ShortRuleRepresentationChange
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_StandardFourierShortSpan
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_RamifiedCoverPairIsomorphism_std_mem_reps
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ReflexNormIndexIdeal_latIdeal_std


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.StandardFourierShortSpan
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient GlobalTheory.IndefiniteRowSideFullHecke.RamifiedCoverPairIsomorphism
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {nab : NabV Xo c}
variable {Δ : DeltaDatum Xo c nab} {hK : ReflexLe Dw c} {nV : ℕ}
  {cusp : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)}
namespace GlobalTheory.IndefiniteRowSideFullHecke.StandardFourierShortSpan
namespace StdFourier
theorem _root_.solution (h : StdFourier Xo c nab) : StdFourierUnit Xo c nab := by
  intro n N β hN hβ
  obtain ⟨b, hb, hs⟩ := hβ.1
  have hu : IsUnit b := by
    rw [latIdeal_std] at hs
    rw [← Ideal.span_singleton_eq_top, hs]
    simp only [reflexIdeal, Ideal.map_top]
    simp [← Ideal.one_eq_top]
  obtain ⟨u, rfl⟩ := hu
  refine ⟨u⁻¹, fun x₀ a P hP => ?_⟩
  have e : (((u⁻¹ : (𝓞 c.F)ˣ) : 𝓞 c.F) : c.F) = β⁻¹ := by
    rw [← hb]
    refine eq_inv_of_mul_eq_one_left ?_
    exact (map_mul (algebraMap (𝓞 c.F) c.F) _ _).symm.trans (by rw [Units.inv_mul, map_one])
  rw [e]
  exact h n N β x₀ a P ⟨std_mem_reps _ n 1, hN, hβ, hP⟩
end StdFourier
end GlobalTheory.IndefiniteRowSideFullHecke.StandardFourierShortSpan
