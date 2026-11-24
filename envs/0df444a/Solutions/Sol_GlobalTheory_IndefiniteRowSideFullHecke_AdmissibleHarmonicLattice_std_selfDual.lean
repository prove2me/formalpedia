-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.std_selfDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:41:47.450647+00:00
-- url     : https://prove2.me/submissions/daa10452-dbdb-46e0-8cf1-40c70c849c99

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
theorem _root_.solution : (Lat.std E n).SelfDual := by
  intro x
  change x ∈ stdMod E n ↔ ∀ y ∈ stdMod E n, _
  constructor
  · intro hx y hy
    rw [mem_stdMod] at hx hy
    choose a ha using hx
    choose b hb using hy
    refine ⟨∑ j, a j * IsCMField.ringOfIntegersComplexConj E (b j), ?_⟩
    simp [stdForm, ← ha, ← hb]
  · intro h
    rw [mem_stdMod]
    intro j
    obtain ⟨a, ha⟩ := h _ (single_mem_stdMod j)
    refine ⟨a, ?_⟩
    rw [ha]
    simp [stdForm, Pi.single_apply, apply_ite]
end GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice
