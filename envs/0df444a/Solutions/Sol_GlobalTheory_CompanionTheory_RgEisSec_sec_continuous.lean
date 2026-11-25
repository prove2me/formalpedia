-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisSec.sec_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:21:18.204496+00:00
-- url     : https://prove2.me/submissions/c9e90652-d471-49be-8b3a-f6e8c1a7a8e7

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_Iwa
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SectionLawHolds
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisSec_isQuotientMap_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisSec_sec_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisSec
variable {G : Type} [Group G] [TopologicalSpace G]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
namespace GlobalTheory.CompanionTheory.RgEisSec
theorem _root_.solution [IsTopologicalGroup G] {Γ K P : Subgroup G} {c : G → ℂ}
    {ρ : K →* (W →L[ℂ] W)} (hK : IsCompact (K : Set G)) (hρ : Continuous ρ) (hpar : IsPar Γ K P c)
    {w : W} (hw : w ∈ secSp K P c ρ) : Continuous fun g => sec K P c ρ g w := by
  refine (isQuotientMap_mul hK hpar.closed hpar.iwa).continuous_iff.mpr ?_
  have hc : Continuous fun p : P => c p := continuousOn_iff_continuous_restrict.mp hpar.ch.cont
  have he : ((fun g => sec K P c ρ g w) ∘ fun x : P × K => (x.1 : G) * (x.2 : G))
      = fun x : P × K => c x.1 • ρ x.2⁻¹ w := by
    funext x
    exact sec_mul hpar.ch hw x.1.2 x.2
  rw [he]
  have h2 : Continuous fun k : K => ρ k⁻¹ w :=
    (hρ.comp continuous_inv).clm_apply continuous_const
  exact (hc.comp continuous_fst).smul (h2.comp continuous_snd)
end GlobalTheory.CompanionTheory.RgEisSec
