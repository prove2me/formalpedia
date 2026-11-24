-- Prove2me | solution 1 for GlobalTheory.PartRed.IntEntry.measurePreserving_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:37:03.758804+00:00
-- url     : https://prove2.me/submissions/2cd6b51c-297f-482c-8c3e-d2a0b6e636cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TranslationInvariantSchwartzBruhatMapFactorsInte
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionIntegrateEntryOfTranslation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.PartRed GlobalTheory.PartRed.IntEntry
namespace GlobalTheory.PartRed.IntEntry
theorem _root_.solution {ι X : Type} [DecidableEq ι] [MeasurableSpace X] (ν : Measure X) [SigmaFinite ν]
    (I : Finset ι) (e : ι) (he : e ∉ I) :
    MeasurePreserving
      (fun (p : X × (I → X)) (i : ↥(insert e I : Finset ι)) => if h : i.1 ∈ I then p.2 ⟨i.1, h⟩ else p.1)
      (ν.prod (Measure.pi fun _ : I => ν)) (Measure.pi fun _ : ↥(insert e I : Finset ι) => ν) := by
  have hm : Measurable
      (fun (p : X × (I → X)) (i : ↥(insert e I : Finset ι)) => if h : i.1 ∈ I then p.2 ⟨i.1, h⟩ else p.1) := by
    refine measurable_pi_lambda _ fun i => ?_
    by_cases h : i.1 ∈ I
    · simp only [dif_pos h]; fun_prop
    · simp only [dif_neg h]; fun_prop
  refine ⟨hm, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun (p : X × (I → X)) (i : ↥(insert e I : Finset ι)) =>
      if h : i.1 ∈ I then p.2 ⟨i.1, h⟩ else p.1) ⁻¹' Set.univ.pi s =
      s ⟨e, Finset.mem_insert_self e I⟩ ×ˢ Set.univ.pi fun i : I => s ⟨i.1, Finset.mem_insert_of_mem i.2⟩ := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff, Set.mem_prod]
    constructor
    · intro h
      refine ⟨by simpa [he] using h ⟨e, Finset.mem_insert_self e I⟩, fun i => ?_⟩
      simpa [i.2] using h ⟨i.1, Finset.mem_insert_of_mem i.2⟩
    · rintro ⟨h1, h2⟩ ⟨i, hi⟩
      by_cases h : i ∈ I
      · simpa [h] using h2 ⟨i, h⟩
      · obtain rfl : i = e := (Finset.mem_insert.1 hi).resolve_right h
        simpa [h] using h1
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Finset.univ_eq_attach (insert e I), Finset.attach_insert,
    Finset.prod_insert, Finset.prod_image, Finset.univ_eq_attach]
  · intro a _ b _ hab
    exact Subtype.ext (congrArg (fun z : ↥(insert e I : Finset ι) => z.1) hab)
  · intro h
    obtain ⟨a, -, ha⟩ := Finset.mem_image.1 h
    have : a.1 = e := congrArg (fun z : ↥(insert e I : Finset ι) => z.1) ha
    exact he (this ▸ a.2)
end GlobalTheory.PartRed.IntEntry
