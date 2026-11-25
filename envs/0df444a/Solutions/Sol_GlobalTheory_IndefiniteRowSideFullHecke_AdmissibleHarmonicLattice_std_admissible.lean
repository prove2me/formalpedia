-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.std_admissible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:54:12.740802+00:00
-- url     : https://prove2.me/submissions/4e9fd129-229a-44bb-ac86-6f37b259ca0c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsThRule
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_AdmissibleHarmonicLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj MvPolynomial
open scoped Pointwise
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
namespace GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice
theorem _root_.solution {H : Host E} (l : Level H) : (Lat.std E n).Admissible l.M l.M := by
  refine ⟨l.odd, dvd_rfl, ?_⟩
  intro x hx
  change x ∈ stdMod E n ⊓ stdMod E n
  rw [inf_idem]
  rw [mulStd, Submodule.mem_smul_pointwise_iff_exists] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact (stdMod E n).smul_mem _ hy
end GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice
