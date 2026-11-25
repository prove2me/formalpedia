-- Prove2me | solution 1 for GlobalTheory.IntegralFrameAllCompare.conclusion_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:30:03.370571+00:00
-- url     : https://prove2.me/submissions/815d5e45-56f8-468f-b3fd-226975964638

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_IntegralFrameAcquisition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_VVNonnegIffLeOne
import Theorems.Thm_GlobalTheory_IntegralFrameAllCompare_extension_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open GlobalTheory GlobalTheory.IntegralFrameAllCompare
open NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.IntegralFrameAcquisition
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)
namespace GlobalTheory.IntegralFrameAllCompare
theorem _root_.solution (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ)
    (ho : OverLa la T.V io e) (y : (letI := io.toAlgebra; FrPt Xo c T.Fr)) :
    (∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (e' : ℕ) (y' : IntFr Xo c T' io'), OverLa la T'.V io' e' ∧ y'.IsAlg ∧
        letI := io.toAlgebra; letI := io'.toAlgebra
        ∃ (φ : T.Fr →ₐ[c.F] T'.Fr) (z : FrPt Xo c T'.Fr) (t : Ix Dw → T'.Frˣ),
          (∀ a : T.V, φ (algebraMap T.V T.Fr a) ∈ Set.range (algebraMap T'.V T'.Fr)) ∧
            FrMap φ y z ∧ FrBor t z y'.1) ↔
      AcquiresIntegralFrame la e y := by
  letI := io.toAlgebra
  constructor
  · rintro ⟨T', io', e', y', ho', ha, φ, z, t, hφ, hz, hb⟩
    letI := io'.toAlgebra
    obtain ⟨j, hj⟩ := φ
    obtain rfl : io' = j.comp io := RingHom.ext fun a => (hj a).symm
    obtain ⟨r, -, hf, ho''⟩ := (extension_iff ho ha j e').1 ⟨ho', hφ⟩
    exact ⟨T', j, r, y', hf, ho'', ha, z, t, hz, hb⟩
  · rintro ⟨T', j, r, y', hf, ho', ha, z, t, hz, hb⟩
    exact ⟨T', j.comp io, r * e, y', ho', ha, algHomOver io j, z, t,
      ((extension_iff ho ha j (r * e)).2 ⟨r, rfl, hf, ho'⟩).2, hz, hb⟩
end GlobalTheory.IntegralFrameAllCompare
