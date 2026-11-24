-- Prove2me | solution 1 for GlobalTheory.X_one_dvd_iff_subst_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:17:59.557661+00:00
-- url     : https://prove2.me/submissions/714a506a-0d09-4d54-9964-c1da0e86530a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SubstTwoVariablesIdentities
import Theorems.Thm_GlobalTheory_hasSubst_pair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPowerSeries
namespace GlobalTheory
theorem _root_.solution {k : Type} [CommRing k] (g : MvPowerSeries (Fin 2) k) :
    X 1 ∣ g ↔ subst (![PowerSeries.X, 0] : Fin 2 → PowerSeries k) g = 0 := by
  have ha : HasSubst (![PowerSeries.X, 0] : Fin 2 → PowerSeries k) :=
    hasSubst_pair PowerSeries.constantCoeff_X (map_zero _)
  constructor
  · rintro ⟨q, rfl⟩
    rw [subst_mul ha, subst_X ha]
    exact zero_mul _
  · intro hg
    have h1 : HasSubst (fun _ : Unit => (X 0 : MvPowerSeries (Fin 2) k)) :=
      hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
    have h2 := subst_comp_subst_apply ha h1 g
    rw [hg, ← coe_substAlgHom h1, map_zero] at h2
    have h3 : rescale (![1, 0] : Fin 2 → k) g = 0 := by
      rw [rescale_eq_subst, h2]
      congr 1
      funext s
      fin_cases s
      · show (1 : k) • (X 0 : MvPowerSeries (Fin 2) k) = substAlgHom h1 (X ())
        rw [substAlgHom_X, one_smul]
      · show (0 : k) • (X 1 : MvPowerSeries (Fin 2) k) = substAlgHom h1 0
        rw [map_zero, zero_smul]
    rw [X_dvd_iff]
    intro m hm
    have h4 := congrArg (coeff m) h3
    rw [coeff_rescale, Finsupp.prod_fintype _ _ (by simp)] at h4
    simpa [hm] using h4
end GlobalTheory
