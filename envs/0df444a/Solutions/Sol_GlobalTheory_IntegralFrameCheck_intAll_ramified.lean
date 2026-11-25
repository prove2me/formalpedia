-- Prove2me | solution 1 for GlobalTheory.IntegralFrameCheck.intAll_ramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:56:53.889269+00:00
-- url     : https://prove2.me/submissions/64781276-6272-4152-845f-d0f342df34d8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllFree
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_VVAlgebraMapNonneg
import Theorems.Thm_GlobalTheory_IntegralFrameCheck_nval_map_of_overLa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IntegralFrameCheck
open Formalism.L2.Pj NumberField IsDedekindDomain
open scoped WithZero
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.IntegralFrameCheck
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (h : Formalism.L2.PjFree.IntAll Xo c)
    (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (ho : OverLa la T.V io e)
    (hf : T.FinRes) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) :
    ∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (r : ℕ) (y' : IntFr Xo c T' io'), 0 < r ∧ OverLa la T'.V io' (r * e) ∧
      T'.FinRes ∧
      letI := io.toAlgebra; letI := io'.toAlgebra
      ∃ (φ : T.Fr →ₐ[c.F] T'.Fr) (z : FrPt Xo c T'.Fr) (t : Ix Dw → T'.Frˣ),
        (∀ x, vV T'.V (φ x) = (r : ℤ) * vV T.V x) ∧ (∀ x, nval T'.V (r * e) (φ x) = nval T.V e x) ∧
        FrMap φ y z ∧ FrBor t z y'.1 := by
  obtain ⟨T', io', e', y', ho', hf', φ, z, t, hφ, hz, hb⟩ := h la T io e ho hf y
  let _ := io.toAlgebra
  let _ := io'.toAlgebra
  obtain ⟨r, hr, rfl, h1, h2⟩ := nval_map_of_overLa ho ho' φ.toRingHom (fun a => φ.commutes a) hφ
  exact ⟨T', io', r, y', hr, ho', hf', φ, z, t, h1, h2, hz, hb⟩
end GlobalTheory.IntegralFrameCheck
