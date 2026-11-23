-- Prove2me | solution 1 for NoHair.scalar_flat_zero_mass_rigidity_three
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T10:50:44.354907+00:00
-- url     : https://prove2.me/submissions/a3e69abb-b539-4633-81bb-d712ed00bea9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_complete_scalar_flat_adm_mass_nonnegative
import Theorems.Thm_NoHair_zero_mass_ricci_flat_by_first_variation
import Theorems.Thm_NoHair_ricci_flat_af_euclidean_developing_cover
import Theorems.Thm_NoHair_global_isometry_of_flat_end_developing_cover
import Definitions.Def_NoHair_scalarFlatMassDeformation

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

noncomputable section

theorem solution : ThreeDimensionalZeroMassRigidity := by
  intro Q m ch sm rb sr rm cm cn sc hend
  have flat := zero_mass_ricci_flat_by_first_variation Q hend complete_scalar_flat_adm_mass_nonnegative
  obtain ⟨d⟩ := ricci_flat_af_euclidean_developing_cover Q hend flat
  exact global_isometry_of_flat_end_developing_cover Q d
