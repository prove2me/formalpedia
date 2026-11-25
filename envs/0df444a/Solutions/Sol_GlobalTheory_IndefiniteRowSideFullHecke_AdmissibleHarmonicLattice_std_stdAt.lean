-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.std_stdAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:53:11.982859+00:00
-- url     : https://prove2.me/submissions/bb471c84-6190-4be0-ab74-a1bb366e4349

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
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice
theorem _root_.solution (s : ℕ) : (Lat.std E n).StdAt s := by
  intro p hp _
  have h1 : ¬ p ∣ 1 := fun h => hp.one_lt.ne' (Nat.dvd_one.1 h)
  exact ⟨fun x hx => ⟨1, h1, by rw [one_smul]; exact hx⟩, fun x hx => ⟨1, h1, by rw [one_smul]; exact hx⟩⟩
end GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice
