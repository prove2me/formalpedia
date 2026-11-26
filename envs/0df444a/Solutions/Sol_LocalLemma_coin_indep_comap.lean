-- Prove2me | solution 1 for LocalLemma.coin_indep_comap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:21:15.287313+00:00
-- url     : https://prove2.me/submissions/cbb91c0f-1bb1-4d15-ad66-e0ea4ac02b05

module
public import Mathlib
public import Definitions.Def_LocalLemmaLib_Coin

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open LocalLemma
namespace LocalLemma
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset ι) :
    Indep (MeasurableSpace.comap (fun ω (i : S) => ω i) MeasurableSpace.pi)
      (MeasurableSpace.comap (fun ω (i : (Sᶜ : Finset ι)) => ω i) MeasurableSpace.pi)
      (coinMeasure ι) := by
  have h : iIndepFun (fun i (ω : ι → Bool) => ω i) (coinMeasure ι) := by
    unfold coinMeasure
    exact iIndepFun_pi (X := fun _ => id) fun _ => aemeasurable_id
  have h2 := h.indepFun_finset S Sᶜ disjoint_compl_right fun i => measurable_pi_apply i
  exact (IndepFun_iff_Indep _ _ _).1 h2
end LocalLemma
