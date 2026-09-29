-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.preconnectedSpace_pullback_g_sigmaA
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/88e474f5-7d55-52a1-b214-ce3add974246

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_preconnectedSpace_pullback_g_sigmaA

set_option autoImplicit false

universe u

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing ModularCurve.JZeroNeronObjectAtP Topology

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) :
    PreconnectedSpace ↥(pullback O.g Λ.σA) := by
  classical
  haveI := O.smooth
  haveI := O.locallyOfFiniteType
  haveI := O.quasiCompact
  let f : pullback O.g Λ.σA ⟶ Spec (CommRingCat.of ↥A) := pullback.snd O.g Λ.σA

  let ηA : Spec (CommRingCat.of ↥A) := ⟨⊥, Ideal.bot_prime⟩
  have hgen : ∀ y : Spec (CommRingCat.of ↥A), ηA ⤳ y := fun y =>
    (PrimeSpectrum.le_iff_specializes ηA y).mp bot_le

  have key : PreconnectedSpace ↥(f.fiber ηA) := by
    let s : ↥(base p) := Λ.σA.base ηA

    haveI hGs : PreconnectedSpace ↥(O.g.fiber s) := by
      have h1 : _root_.IsPreconnected (Set.range (O.g.fiberι s).base) := by
        rw [Scheme.Hom.range_fiberι]; exact O.fibre_preconnected s
      rw [← Set.image_univ] at h1
      exact ⟨((O.g.fiberι s).isEmbedding.isInducing.isPreconnected_image).mp h1⟩

    haveI : LocallyOfFiniteType (O.g.fiberToSpecResidueField s) := by
      delta Scheme.Hom.fiberToSpecResidueField Scheme.Hom.fiber; infer_instance
    haveI : QuasiCompact (O.g.fiberToSpecResidueField s) := by
      delta Scheme.Hom.fiberToSpecResidueField Scheme.Hom.fiber; infer_instance
    obtain ⟨G₀, i, L₀, -, -, -, -, -, hrange, hK, -⟩ :=
      GoodReductionJacobian.RelativeGroupLaw.exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent
        (↥((base p).residueField s)) (f := O.g.fiberToSpecResidueField s)
        (O.L.baseChange ((base p).fromSpecResidueField s))
    have hr : Set.range i.base = Set.univ := by
      rw [hrange]; exact PreconnectedSpace.connectedComponent_eq_univ _
    have hKt := hK (↥((Spec (CommRingCat.of ↥A)).residueField ηA)) (Spec.map (Λ.σA.residueFieldMap ηA))
    rw [hr, Set.preimage_univ] at hKt
    have hP : PreconnectedSpace
        ↥(pullback (O.g.fiberToSpecResidueField s) (Spec.map (Λ.σA.residueFieldMap ηA))) :=
      ⟨by rw [hKt]; exact isPreconnected_connectedComponent⟩

    have sq := isPullback_fiberToSpecResidueField_of_isPullback (IsPullback.of_hasPullback O.g Λ.σA) ηA
    let ι' := sq.isoPullback.inv
    have hsurj : Function.Surjective ι'.base := ι'.surjective
    have hr2 := hP.isPreconnected_univ.image ι'.base ι'.continuous.continuousOn
    exact ⟨(Set.image_univ_of_surjective hsurj) ▸ hr2⟩
  have hF : _root_.IsPreconnected (f.base ⁻¹' {ηA}) := by
    rw [← Scheme.Hom.range_fiberι]
    haveI := key
    exact isPreconnected_range (f.fiberι ηA).continuous

  have hcl : closure (f.base ⁻¹' {ηA}) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨z, hzx, hz⟩ := Flat.generalizingMap f (hgen (f.base x))
    have hx : x ∈ closure ({z} : Set ↥(pullback O.g Λ.σA)) := specializes_iff_mem_closure.mp hzx
    have hz' : ({z} : Set ↥(pullback O.g Λ.σA)) ⊆ f.base ⁻¹' {ηA} := Set.singleton_subset_iff.mpr hz
    exact closure_mono hz' hx
  exact ⟨by rw [← hcl]; exact hF.closure⟩

end S_ModularCurve_JZeroNeronObjectAtP_preconnectedSpace_pullback_g_sigmaA
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_preconnectedSpace_pullback_g_sigmaA (solution)
