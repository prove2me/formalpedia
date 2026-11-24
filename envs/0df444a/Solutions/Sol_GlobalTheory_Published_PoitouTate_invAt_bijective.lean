-- Prove2me | solution 1 for GlobalTheory.Published.PoitouTate.invAt_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:40:02.4058+00:00
-- url     : https://prove2.me/submissions/bb1427fb-21b2-48db-9015-64379a4d1139

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Theorems.Thm_GlobalTheory_Published_PoitouTate_toMuLoc_bijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.PoitouTate
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {r : ℕ} (S : Finset (HeightOneSpectrum (𝓞 F)))
  (Av : S → ValuationSubring Ω)
  (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
namespace GlobalTheory.Published.PoitouTate
theorem _root_.solution (hμ : μ.comp (toGS Ω _) = cycMod F Ω l r) {ζ : Ω} {inv : InvFam F Ω l r}
    (h : IsLocalInvariants ζ inv) (v : S) (hv : IsPlaceOver (Av v) v.1) :
    Function.Bijective (invAt S Av μ hμ inv v) := by
  rw [invAt, LinearMap.coe_comp]
  exact (h.1 (Av v) v.1 hv).1.comp (toMuLoc_bijective S Av μ hμ v)
end GlobalTheory.Published.PoitouTate
