-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Transv.measurePreserving_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:58:40.056274+00:00
-- url     : https://prove2.me/submissions/8d387438-8b37-42ee-8a3f-efa60ebab58f

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HaarInvariantUnderTransvection
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Transv_toMatrix_mulVec_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Transv
namespace GlobalTheory.CompanionTheory.SW.Transv
theorem _root_.solution {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
    {ι : Type} [Fintype ι] [DecidableEq ι] (ν : Measure K) [SigmaFinite ν]
    [ν.IsAddLeftInvariant] (t : Matrix.TransvectionStruct ι K) :
    MeasurePreserving (fun x : ι → K => t.toMatrix *ᵥ x)
      (Measure.pi fun _ : ι => ν) (Measure.pi fun _ : ι => ν) := by
  classical
  have hj : t.j ≠ t.i := t.hij.symm
  let p : ι → Prop := fun k => k ≠ t.i
  let B : Measure ({k // p k} → K) := Measure.pi fun _ => ν
  let A : Measure ({k // ¬ p k} → K) := Measure.pi fun _ => ν
  have hmp := measurePreserving_piEquivPiSubtypeProd (fun _ : ι => ν) p
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => K) p
  let g : ({k // p k} → K) → ({k // ¬ p k} → K) → ({k // ¬ p k} → K) :=
    fun b a => (fun _ => t.c * b ⟨t.j, hj⟩) + a
  have hgm : Measurable (Function.uncurry g) := by
    refine measurable_pi_iff.2 fun k => ?_
    have h1 : Measurable fun q : ({k // p k} → K) × ({k // ¬ p k} → K) =>
        q.1 ⟨t.j, hj⟩ := (measurable_pi_apply _).comp measurable_fst
    have h2 : Measurable fun q : ({k // p k} → K) × ({k // ¬ p k} → K) =>
        q.2 k := (measurable_pi_apply _).comp measurable_snd
    exact (h1.const_mul t.c).add h2
  have hsk : MeasurePreserving (fun q : ({k // p k} → K) × ({k // ¬ p k} → K) => (id q.1, g q.1 q.2))
      (B.prod A) (B.prod A) := by
    refine (MeasurePreserving.id B).skew_product hgm (Filter.Eventually.of_forall fun b => ?_)
    exact map_add_left_eq_self A _
  have hall := hmp.symm.comp (hsk.comp hmp)
  have hfun : (fun x : ι → K => t.toMatrix *ᵥ x) =
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => K) p).symm ∘
        (fun q : ({k // p k} → K) × ({k // ¬ p k} → K) => (id q.1, g q.1 q.2)) ∘
          (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => K) p) := by
    funext x k
    rw [toMatrix_mulVec_apply]
    by_cases hk : k = t.i
    · subst hk
      have hnp : ¬ p t.i := fun h => h rfl
      simp [MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, g, hnp, add_comm]
    · have hp : p k := hk
      simp [MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hp, hk]
  rw [hfun]
  exact hall
end GlobalTheory.CompanionTheory.SW.Transv
