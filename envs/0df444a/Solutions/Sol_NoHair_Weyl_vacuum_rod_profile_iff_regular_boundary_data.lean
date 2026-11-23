-- Prove2me | solution 1 for NoHair.Weyl.vacuum_rod_profile_iff_regular_boundary_data
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T10:34:14.825694+00:00
-- url     : https://prove2.me/submissions/cdb70397-8096-496e-b65d-d98270c9e457

import Theorems.Thm_NoHair_Weyl_kerr_weyl_model
import Theorems.Thm_NoHair_Weyl_kerr_boundary_profile_estimates
import Theorems.Thm_NoHair_Weyl_comparison_of_common_boundary_profile
import Theorems.Thm_NoHair_Weyl_vacuum_ernst_boundary_uniqueness
import Theorems.Thm_NoHair_Weyl_kerr_regular_rod_boundary_data
import Theorems.Thm_NoHair_Weyl_profile_of_regular_rod_boundary_data

open NoHair NoHair.Weyl Set

theorem solution (u : ErnstPotentials) (m a : ℝ) (hm : IsKerrNewmanBlackHoleParams m a 0)
    (hu : u.IsSolution) :
    let ℓ := Real.sqrt (m^2-a^2)
    let J := m*a
    HasProfileEstimates u (rodBoundaryProfile m ℓ J) ↔ Nonempty (RegularRodBoundaryData u m ℓ J) := by
  let ℓ := Real.sqrt (m^2-a^2)
  let b := rodBoundaryProfile m ℓ (m*a)
  let K := kerrErnst m a
  obtain ⟨hsol,_,_,_⟩ := kerr_weyl_model m a hm
  obtain ⟨hK,hmodel⟩ := kerr_boundary_profile_estimates m a hm
  constructor
  · intro hp
    have hbounds := (comparison_of_common_boundary_profile u K b (fun p => (hmodel p).1) hp hK).1
    have heq : u = K := vacuum_ernst_boundary_uniqueness u K hu hsol hbounds
    rw [heq]
    exact kerr_regular_rod_boundary_data m a hm
  · rintro ⟨bd⟩
    exact profile_of_regular_rod_boundary_data u m ℓ (m*a) hm.1 (Real.sqrt_nonneg _) bd
