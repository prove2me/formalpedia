-- Prove2me | solution 1 for GroundTheory.Global.localAverage_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:46:01.19952+00:00
-- url     : https://prove2.me/submissions/b2341893-d3a5-42e6-b55c-04a114e6c899

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_LogCharpoly
import Definitions.Def_GroundTheory_GlobalFields_Artin_MemInvariantsCompSubtypeIff
import Theorems.Thm_GroundTheory_Global_cosetAverage_inertia_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField Polynomial
open scoped Pointwise
open GroundTheory GroundTheory.Global
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (v : HeightOneSpectrum (𝓞 K))
namespace GroundTheory.Global
theorem _root_.solution (f : Gal(L/K) → ℂ) (hf : ∀ g h, f (h * g * h⁻¹) = f g)
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] {φ : Gal(L/K)}
    (hφ : IsArithFrobAt (𝓞 K) φ w.asIdeal) (m : ℕ) :
    localAverage L v f m = cosetAverage (w.asIdeal.inertia Gal(L/K)) f (φ ^ m) :=
  cosetAverage_inertia_eq v f hf w (placeAbove v) hφ (IsArithFrobAt.arithFrobAt _ _ _) m
end GroundTheory.Global
