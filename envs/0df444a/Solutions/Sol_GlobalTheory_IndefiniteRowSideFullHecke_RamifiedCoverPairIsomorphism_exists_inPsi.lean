-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.RamifiedCoverPairIsomorphism.exists_inPsi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:40:27.86253+00:00
-- url     : https://prove2.me/submissions/c6fdee6b-2ce0-4d69-92ed-3441a313c5cf

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ReflexNormIndexIdeal
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_NormFactorThetaValue
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_DeltaDatumCombinedCoefficient
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ShortRuleRepresentationChange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.RamifiedCoverPairIsomorphism
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation GlobalTheory.IndefiniteRowSideFullHecke.NormFactorThetaValue GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {nab : NabV Xo c} (Δ : DeltaDatum Xo c nab)
namespace GlobalTheory.IndefiniteRowSideFullHecke.RamifiedCoverPairIsomorphism
theorem _root_.solution (H : Host E) : ∃ τ : E →+* ℂ, InPsi H τ := by
  obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  have e : (τ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
    have h0 := congrArg (fun x : 𝓞 E => τ (x : E)) H.rt_sq
    simpa using h0
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (e.trans H.sqrt_neg_disc_sq.symm) with h | h
  · exact ⟨τ, h⟩
  · refine ⟨(starRingEnd ℂ).comp τ, ?_⟩
    show starRingEnd ℂ (τ (H.rt : E)) = H.rt0
    rw [h, map_neg]
    have hs := H.sqrt_neg_disc_sq
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    have h1 := congrArg Complex.re hs
    have h2 := congrArg Complex.im hs
    simp [sq] at h1 h2
    have hre : H.rt0.re = 0 := by
      rcases mul_eq_zero.1 (show H.rt0.re * H.rt0.im = 0 by nlinarith [h2]) with h3 | h3
      · exact h3
      · rw [h3] at h1
        nlinarith [sq_nonneg H.rt0.re]
    apply Complex.ext <;> simp [hre]
end GlobalTheory.IndefiniteRowSideFullHecke.RamifiedCoverPairIsomorphism
