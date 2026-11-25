-- Prove2me | solution 1 for GlobalTheory.NoetherInt.quasiFinite_of_isUnit_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:39:40.816943+00:00
-- url     : https://prove2.me/submissions/57d07d8a-5525-4ec9-9dc0-105617ee387e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsQuasiFinitePolynomialMap
import Theorems.Thm_P2M_GlobalTheory_NoetherInt_quasiFinite_of_eval__eq_zero_2e2ddb8bdce6

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NoetherInt
open Polynomial
namespace GlobalTheory.NoetherInt
theorem _root_.solution {R T : Type*} [CommRing R] [CommRing T] (φ : R →+* T) (t : T)
    (h : (eval₂RingHom φ t).QuasiFinite) (G : R[X]) (hG : eval₂ φ t G = 0) (k : ℕ)
    (hc : IsUnit (φ (G.coeff k))) : φ.QuasiFinite := by
  let c := G.coeff k
  let φ' : Localization.Away c →+* T := IsLocalization.Away.lift c hc
  have hφ : φ'.comp (algebraMap R (Localization.Away c)) = φ := IsLocalization.Away.lift_comp c hc
  have hφx : ∀ a, φ' (algebraMap R (Localization.Away c) a) = φ a := fun a => by
    rw [← RingHom.comp_apply, hφ]
  have hι : (eval₂RingHom φ' t).comp (mapRingHom (algebraMap R (Localization.Away c)))
      = eval₂RingHom φ t := by
    ext <;> simp [hφx]
  have h1 : (eval₂RingHom φ' t).QuasiFinite := RingHom.QuasiFinite.of_comp
    (g := mapRingHom (algebraMap R (Localization.Away c))) (hι ▸ h)
  have hG' : eval₂ φ' t (G.map (algebraMap R (Localization.Away c))) = 0 := by
    have h5 := DFunLike.congr_fun hι G
    simpa [hG] using h5
  have h2 : φ'.QuasiFinite := quasiFinite_of_eval₂_eq_zero φ' t h1 _ hG' k (by
    rw [coeff_map]; exact IsLocalization.Away.algebraMap_isUnit c)
  have h3 : (algebraMap R (Localization.Away c)).QuasiFinite :=
    RingHom.quasiFinite_algebraMap.2 (.of_isLocalization (.powers c))
  exact hφ ▸ h2.comp h3
end GlobalTheory.NoetherInt
