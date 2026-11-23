-- Prove2me | solution 1 for GlobalTheory.QNorm.finite_valuation_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:29.21794+00:00
-- url     : https://prove2.me/submissions/1a085a9e-4438-4e79-9e80-e3e743325976

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSupersetMemSUnits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution (F : Type) [Field F] [NumberField F] (x : Fˣ) :
    {v : HeightOneSpectrum (𝓞 F) | v.valuation F (x : F) ≠ 1}.Finite := by
  refine ((HeightOneSpectrum.Support.finite (𝓞 F) (x : F)).union
    (HeightOneSpectrum.Support.finite (𝓞 F) ((x : F)⁻¹))).subset ?_
  intro v hv
  have hv' : v.valuation F (x : F) ≠ 1 := hv
  have h0 : v.valuation F (x : F) ≠ 0 := by
    rw [Ne, map_eq_zero]
    exact x.ne_zero
  rcases lt_or_gt_of_ne hv' with h | h
  · right
    show 1 < v.valuation F ((x : F)⁻¹)
    rw [map_inv₀]
    exact one_lt_inv₀ (zero_lt_iff.mpr h0) |>.mpr h
  · left
    exact h
end GlobalTheory.QNorm
