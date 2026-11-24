-- Prove2me | solution 1 for GlobalTheory.ArtinTransport.normV_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:59:04.234327+00:00
-- url     : https://prove2.me/submissions/7934d184-0722-4b50-a564-e6afc5733b62

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FrobeniusRestrictScalarsPowModInertia
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ArtinTransportAlgClosureEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
noncomputable section
open GlobalTheory GlobalTheory.ArtinTransport
open scoped Pointwise
variable {E Ω E' Ω' : Type} [Field E] [Field Ω] [Algebra E Ω] [Field E'] [Field Ω'] [Algebra E' Ω'] [Algebra E E']
namespace GlobalTheory.ArtinTransport
theorem _root_.solution [NumberField E] [NumberField E'] {v : HeightOneSpectrum (𝓞 E)} {w : HeightOneSpectrum (𝓞 E')}
    (hwv : w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 E')) = v.asIdeal) :
    normV w = normV v ^ w.asIdeal.inertiaDeg (𝓞 E) := by
  have : w.asIdeal.LiesOver v.asIdeal := ⟨hwv.symm⟩
  simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  exact (Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal).symm
end GlobalTheory.ArtinTransport
