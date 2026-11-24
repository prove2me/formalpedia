-- Prove2me | solution 1 for GlobalTheory.SameZeroScheme.dvd_on_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:47:04.798559+00:00
-- url     : https://prove2.me/submissions/5716ee57-576b-4580-a7d4-91c57c4abc12

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsUnitMul
import Theorems.Thm_GlobalTheory_SameZeroScheme_appLE_spec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SameZeroScheme
namespace GlobalTheory.SameZeroScheme
theorem _root_.solution {Y : Scheme.{0}} {U V : Y.Opens} (hU : IsAffineOpen U) (h : U ≤ V)
    (a b : Γ(Y, V))
    (H : ∀ (T : Scheme.{0}) (t : T ⟶ Y) (h : ⊤ ≤ t ⁻¹ᵁ V),
      (t.appLE V ⊤ h).hom a = 0 → (t.appLE V ⊤ h).hom b = 0) :
    resG Y h a ∣ resG Y h b := by
  let I : Ideal Γ(Y, U) := Ideal.span {resG Y h a}
  let φ : Γ(Y, U) ⟶ CommRingCat.of (Γ(Y, U) ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I)
  have key := H _ _ (top_le_preimage hU h φ)
  rw [appLE_spec hU h φ] at key
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, U) ⧸ I))).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, U) ⧸ I))).commRingCatIsoToRingEquiv.symm.injective
  have ha : Ideal.Quotient.mk I (resG Y h a) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  have hb := key (by
    change (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, U) ⧸ I))).inv.hom
      (Ideal.Quotient.mk I (resG Y h a)) = 0
    rw [ha]; exact map_zero _)
  have hb' : Ideal.Quotient.mk I (resG Y h b) = 0 :=
    hinj (hb.trans (map_zero _).symm)
  exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 hb')
end GlobalTheory.SameZeroScheme
