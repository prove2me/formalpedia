-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal.latIdeal_std
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:34.869867+00:00
-- url     : https://prove2.me/submissions/64c11586-cebe-4f75-bf51-594d4be1c0ad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_AdmissibleHarmonicLattice
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ReflexNormIndexIdeal

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
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
omit [IsCMField E]
namespace GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal
theorem _root_.solution : latIdeal (Lat.std E n) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  exact Ideal.subset_span ⟨LinearMap.id, fun x hx => ⟨hx, hx⟩, by simp⟩
end GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal
