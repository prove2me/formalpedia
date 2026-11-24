-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Mass.MeanV.Den.exists_pow_mul_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:51:05.96268+00:00
-- url     : https://prove2.me/submissions/ff9cab8d-8325-4758-b980-9e064a7d0350

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TruncSum
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsIntegralMultipleBoundedPlaces

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Mass GlobalTheory.CompanionTheory.Mass.MeanV GlobalTheory.CompanionTheory.Mass.MeanV.Den
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.Mass.MeanV.Den
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v)
    (ha : Valued.v a < 1) (K : Set (Fv F v)) (hK : IsCompact K) :
    ∃ m : ℕ, ∀ s ∈ K, Valued.v (a ^ m * s) ≤ 1 := by
  have h1 : IsOpen {s : Fv F v | Valued.v s < 1} := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    rw [Valued.mem_nhds]
    refine ⟨1, fun y hy => ?_⟩
    have hy' : Valued.v (y - x) < 1 := by simpa using hy
    have h := Valuation.map_add_lt Valued.v hy' hx
    simpa using h
  have h2 : Tendsto (fun m : ℕ => a ^ m) atTop (𝓝 0) := Valued.tendsto_zero_pow_of_v_lt_one ha
  have hUo : ∀ m : ℕ, IsOpen {s : Fv F v | Valued.v (a ^ m * s) < 1} := fun m =>
    (continuous_const.mul continuous_id).isOpen_preimage _ h1
  have hcover : ∀ s : Fv F v, ∃ m : ℕ, Valued.v (a ^ m * s) < 1 := by
    intro s
    have h0 : Tendsto (fun m : ℕ => a ^ m * s) atTop (𝓝 0) := by
      simpa using h2.mul_const s
    have hn : {y : Fv F v | Valued.v y < 1} ∈ 𝓝 (0 : Fv F v) := h1.mem_nhds (by simp)
    exact (h0.eventually hn).exists
  have hmono : Monotone fun m : ℕ => {s : Fv F v | Valued.v (a ^ m * s) < 1} := by
    intro m m' hmm' s hs
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmm'
    show Valued.v (a ^ (m + d) * s) < 1
    rw [show a ^ (m + d) * s = a ^ d * (a ^ m * s) by ring, Valuation.map_mul, map_pow]
    calc Valued.v a ^ d * Valued.v (a ^ m * s) ≤ 1 * Valued.v (a ^ m * s) :=
by
          gcongr
          first
            | exact pow_le_one₀ zero_le ha.le
            | exact pow_le_one₀ zero_le' ha.le
      _ = Valued.v (a ^ m * s) := one_mul _
      _ < 1 := hs
  obtain ⟨m, hm⟩ := hK.elim_directed_cover (fun m : ℕ => {s : Fv F v | Valued.v (a ^ m * s) < 1}) hUo
    (fun s _ => Set.mem_iUnion.mpr (hcover s)) hmono.directed_le
  exact ⟨m, fun s hs => le_of_lt (hm hs)⟩
end GlobalTheory.CompanionTheory.Mass.MeanV.Den
