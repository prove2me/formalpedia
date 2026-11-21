-- Prove2me | solution 1 for MasulloRH.spectral_trace_hasSum
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:24:12.801546+00:00
-- url     : https://prove2.me/submissions/7c558f1a-e566-4cf3-8f1e-bbe4b7795197
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_unrestricted_spectral_hasSum
import Theorems.Thm_MasulloRH_weilDistribution_eq_rational_geometric
import Theorems.Thm_MasulloRH_omitted_spectral_mass_zero

open Set MeasureTheory MasulloRH

theorem solution (α : ℝ) (hα : 0 < α) (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    HasSum (zetaTraceTerm φ α) ((mellin φ (1 / 2) + mellin φ (-1 / 2)) -
      ((∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
        ∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i)) := by
  let Z := {z : ℂ // ConnesRZ.IsCriticalZero z}
  let S : Set Z := {z | |z.val.re - 1/2| < α}
  let f (z : Z) := (ConnesRZ.zeroMult z.val : ℂ) * mellin φ (z.val - 1/2)
  let e : ZetaZerosInTraceStrip α ≃ S :=
    { toFun := fun z => ⟨⟨z.val, z.property.1, z.property.2.1, z.property.2.2.1⟩, z.property.2.2.2⟩
      invFun := fun z => ⟨z.val.val, z.val.property.1, z.val.property.2.1, z.val.property.2.2, z.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hall : HasSum f (ConnesRZ.weilDistribution (fun u => φ (Real.exp u))) :=
    unrestricted_spectral_hasSum φ hφ
  have hzero : (∑' z : ↥(Sᶜ), f z.val) = 0 := omitted_spectral_mass_zero α hα φ hφ
  have hs := hall.summable.tsum_subtype_add_tsum_subtype_compl S
  rw [hzero, add_zero, hall.tsum_eq, weilDistribution_eq_rational_geometric φ hφ] at hs
  have hsub := (hall.summable.subtype (· ∈ S)).hasSum
  rw [← hs]
  exact e.hasSum_iff.mpr hsub
