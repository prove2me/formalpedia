-- Prove2me | solution 1 for GroundTheory.Global.cosetAverage_inertia_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:16:16.816816+00:00
-- url     : https://prove2.me/submissions/5e777327-82f7-4179-a113-2e69a548b2cf

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_LogCharpoly
import Definitions.Def_GroundTheory_GlobalFields_Artin_MemInvariantsCompSubtypeIff
import Theorems.Thm_GroundTheory_Global_cosetAverage_mul_of_mem
import Theorems.Thm_GroundTheory_Global_cosetAverage_conj
import Theorems.Thm_GroundTheory_Global_inv_pow_mul_pow_mem_inertia

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
    (w w' : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    [w'.asIdeal.LiesOver v.asIdeal] {φ φ' : Gal(L/K)} (hφ : IsArithFrobAt (𝓞 K) φ w.asIdeal)
    (hφ' : IsArithFrobAt (𝓞 K) φ' w'.asIdeal) (m : ℕ) :
    cosetAverage (w'.asIdeal.inertia Gal(L/K)) f (φ' ^ m) =
      cosetAverage (w.asIdeal.inertia Gal(L/K)) f (φ ^ m) := by
  obtain ⟨h, hh⟩ := Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal w.asIdeal w'.asIdeal Gal(L/K)
  have hψ : IsArithFrobAt (𝓞 K) (h * φ * h⁻¹) w'.asIdeal := hh ▸ hφ.conj h
  have hI := inv_pow_mul_pow_mem_inertia hψ.mem_stabilizer (hφ'.mul_inv_mem_inertia hψ) m
  rw [← mul_inv_cancel_left ((h * φ * h⁻¹) ^ m) (φ' ^ m), cosetAverage_mul_of_mem _ _ _ hI,
    conj_pow]
  refine cosetAverage_conj _ _ f hf h (fun σ => ?_) _
  rw [← hh, mem_inertia_smul_iff]
end GroundTheory.Global
