-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Mass.MeanV.exists_common_denominator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:08:26.113077+00:00
-- url     : https://prove2.me/submissions/47c6fe91-f697-48bf-bb36-712eca15a09b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TruncSum
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsIntegralMultipleBoundedPlaces
import Theorems.Thm_GlobalTheory_CompanionTheory_Mass_MeanV_Den_exists_pow_mul_le_one
import Theorems.Thm_GlobalTheory_CompanionTheory_Mass_MeanV_Den_exists_nat_lt_one
import Theorems.Thm_GlobalTheory_CompanionTheory_Mass_MeanV_Den_val_nat_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
namespace GlobalTheory.CompanionTheory.Mass.MeanV
theorem _root_.solution :
    ∀ (F : Type) [Field F] [NumberField F] (T : Finset (HeightOneSpectrum (𝓞 F))) (K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)), (∀ v ∈ T, IsCompact (K v)) → ∃ N : ℕ, 0 < N ∧ ∀ x ∈ IntOut T, (∀ v ∈ T, algebraMap F (Fv F v) x ∈ K v) → ∃ y : 𝓞 F, (y : F) = (N : F) * x := by
  intro F _ _ T K hK
  have h3 : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : F), Valued.v (algebraMap F (Fv F v) x) = v.valuation F x := by
    intro v x
    show Valued.v ((x : v.adicCompletion F)) = v.valuation F x
    first
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' x
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) x
  have h4 : ∀ x : F, (∀ v : HeightOneSpectrum (𝓞 F), v.valuation F x ≤ 1) → ∃ y : 𝓞 F, (y : F) = x := by
    intro x hx
    obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) (x := x) (h := hx)
    exact ⟨y, hy⟩
  have hpl : ∀ (v : HeightOneSpectrum (𝓞 F)) (n k : ℕ), v.valuation F ((n : F) ^ k) ≤ 1 := by
    intro v n k
    rw [← Nat.cast_pow]
    exact Den.val_nat_le_one v _
  choose p hp0 hp1 using fun v : HeightOneSpectrum (𝓞 F) => Den.exists_nat_lt_one v
  have hm : ∀ v ∈ T, ∃ m : ℕ, ∀ s ∈ K v, Valued.v (algebraMap F (Fv F v) (p v : F) ^ m * s) ≤ 1 :=
    fun v hv => Den.exists_pow_mul_le_one v _ (by rw [h3]; exact hp1 v) (K v) (hK v hv)
  choose! m hm using hm
  refine ⟨∏ v ∈ T, p v ^ m v, Finset.prod_pos fun v _ => pow_pos (hp0 v) _, ?_⟩
  intro x hx hxK
  apply h4
  intro w
  push_cast
  rw [map_mul]
  by_cases hw : w ∈ T
  · rw [← Finset.mul_prod_erase T (fun v => (p v : F) ^ m v) hw, map_mul, map_prod]
    have hrest : ∏ v ∈ T.erase w, w.valuation F ((p v : F) ^ m v) ≤ 1 :=
      Finset.prod_le_one' fun v _ => hpl w (p v) (m v)
    have hmain : w.valuation F ((p w : F) ^ m w) * w.valuation F x ≤ 1 := by
      have h := hm w hw _ (hxK w hw)
      rw [← map_pow, ← map_mul, h3, map_mul] at h
      exact h
    calc w.valuation F ((p w : F) ^ m w) * (∏ v ∈ T.erase w, w.valuation F ((p v : F) ^ m v)) *
          w.valuation F x
        = (∏ v ∈ T.erase w, w.valuation F ((p v : F) ^ m v)) *
            (w.valuation F ((p w : F) ^ m w) * w.valuation F x) := by ac_rfl
      _ ≤ 1 * 1 := mul_le_mul' hrest hmain
      _ = 1 := one_mul 1
  · have hxw : w.valuation F x ≤ 1 := by
      have h : Valued.v (algebraMap F (Fv F w) x) ≤ 1 := hx w hw
      rwa [h3] at h
    have hN : w.valuation F (∏ v ∈ T, (p v : F) ^ m v) ≤ 1 := by
      rw [map_prod]
      exact Finset.prod_le_one' fun v _ => hpl w (p v) (m v)
    calc w.valuation F (∏ v ∈ T, (p v : F) ^ m v) * w.valuation F x ≤ 1 * 1 := mul_le_mul' hN hxw
      _ = 1 := one_mul 1
end GlobalTheory.CompanionTheory.Mass.MeanV
