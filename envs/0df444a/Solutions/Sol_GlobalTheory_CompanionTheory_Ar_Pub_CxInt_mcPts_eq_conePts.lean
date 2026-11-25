-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Pub.CxInt.mcPts_eq_conePts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:43:01.121802+00:00
-- url     : https://prove2.me/submissions/d7d3adc7-2a3b-47df-9c43-5a6baafd7256

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Metrics__SheetDensityEqSetSheetDensity_cb85824e9bfdd8ba

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Pub
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open GlobalTheory.CompanionTheory.Ar.Pub.CxInt
namespace GlobalTheory.CompanionTheory.Ar.Pub.CxInt
theorem _root_.solution {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) :
    mcPts P = ReciprocityTheory.AnForm.R.conePts (P.map (map (Int.castRingHom ℂ) : MRing ι →+* MRingOver ℂ ι)) := by
  ext z
  simp only [mcPts, ReciprocityTheory.AnForm.R.conePts, Set.mem_setOf_eq]
  refine and_congr_right fun _ => ⟨fun h f hf => ?_, fun h f hf => h _ (Ideal.mem_map_of_mem _ hf)⟩
  have hle : P ≤ Ideal.comap (map (Int.castRingHom ℂ) : MRing ι →+* MRingOver ℂ ι)
      (RingHom.ker (eval z)) :=
    fun g hg => Ideal.mem_comap.mpr (RingHom.mem_ker.mpr (h g hg))
  exact RingHom.mem_ker.mp (Ideal.map_le_of_le_comap hle hf)
end GlobalTheory.CompanionTheory.Ar.Pub.CxInt
