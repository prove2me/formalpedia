-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisPar.parLaw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:25:16.033091+00:00
-- url     : https://prove2.me/submissions/87d2b203-fc70-4862-bfdb-e907616870c2

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ParabolicLawOfBlockDet
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisPar_stab_univ_eq_top
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisPar_isCh_of_top
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisPar_isCh_cGL
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisPar_ext_gl
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisPar_closed_uQ
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisPar_ext_u
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisPar_isCh_uC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisPar
variable {E R : Type} [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  [LocallyCompactSpace R] [SecondCountableTopology R]
namespace GlobalTheory.CompanionTheory.RgEisPar
theorem _root_.solution : BdetLaw → ExtLaw → GrpTop → ParLaw := by
  intro hB hE hT E R _ _ _ _ _ _ _ A hA ι _ _ ε s
  obtain ⟨hc, -⟩ := hB E R A hA.toGoodL ι s
  have hch := isCh_cGL hB A hA.toGoodL ι
  refine ⟨⟨⟨hc, hA.iwa ι s, ?_⟩, ⟨hc, hA.iwa ι s, isCh_of_top hch⟩, hch, (ext_gl hB hE hT A hA ι s).1, stab_univ_eq_top⟩, ?_⟩
  · refine ⟨fun _ _ _ _ => by simp, fun _ _ => by simp, fun _ _ _ => rfl, continuousOn_const⟩
  intro hI
  have hI' : Iwa (A.uQ ε s) (A.uK ε ι) := fun g => by
    obtain ⟨p, hp, k, hk, e⟩ := hI g
    exact ⟨p, hp.1, k, hk, e⟩
  have hu := ext_u hB hE hT A hA ε s hI'
  have hC := isCh_uC hB A hA.toGoodL (ε := ε) (κ := ι)
  refine ⟨⟨(closed_uQ hB A hA.toGoodL ε s).inter (closed_uQ hB A hA.toGoodL ε Set.univ), hI, ?_⟩, hu.1, fun g => ?_⟩
  · exact ⟨fun p hp q hq => hC.mul p hp.2 q hq.2, fun p hp => hC.norm p hp.2, fun γ hγ hp => hC.rat γ hγ hp.2,
      hC.cont.mono fun _ h => h.2⟩
  · obtain ⟨p, hp, k, hk, rfl⟩ := hI' g
    rw [hu.2 p hp k hk]
    exact ((ext_gl hB hE hT A hA (ι ⊕ ι) (Sum.inl '' s)).2 p.1 hp k.1 hk).symm
end GlobalTheory.CompanionTheory.RgEisPar
