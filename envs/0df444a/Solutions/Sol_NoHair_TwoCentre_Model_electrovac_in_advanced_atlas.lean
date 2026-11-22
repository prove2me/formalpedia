-- Prove2me | solution 1 for NoHair.TwoCentre.Model.electrovac_in_advanced_atlas
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T22:17:52.19801+00:00
-- url     : https://prove2.me/submissions/3af3feb8-3806-4fcb-8c9c-861c04f5675a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_TwoCentre_Model_electrovac_across_horizon
import Theorems.Thm_NoHair_TwoCentre_Model_advanced_exterior_equations

open NoHair NoHair.TwoCentre NoHair.TwoCentre.Model

theorem solution (h : ∀ y ∈ exterior, EinsteinMaxwellAt isotropicMetric TwoCentre.field y) :
    IsElectrovac metric faraday := electrovac_across_horizon (advanced_exterior_equations h)
