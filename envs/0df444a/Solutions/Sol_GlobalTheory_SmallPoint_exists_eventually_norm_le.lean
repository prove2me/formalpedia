-- Prove2me | solution 1 for GlobalTheory.SmallPoint.exists_eventually_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:50:20.791674+00:00
-- url     : https://prove2.me/submissions/7dc7b0f9-3393-4aaf-befe-d36ad36b6a8c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SpecialisationNumberFieldAndCountableValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowCardLeNormProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsComplexPointNormLtOfNotIsUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Topology
open GlobalTheory
open GlobalTheory.SmallPoint
namespace GlobalTheory.SmallPoint
theorem _root_.solution {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (Ψ : R →+* ℂ[X]) {b : B} (hb : IsIntegral R b) :
    ∃ M : ℝ, ∀ᶠ s in 𝓝 (0 : ℂ), ∀ φ : B →+* ℂ,
      φ.comp (algebraMap R B) = (evalRingHom s).comp Ψ → ‖φ b‖ ≤ M := by
  obtain ⟨G, hG, hGb⟩ := hb
  have h1 : ∀ i : ℕ, ∀ᶠ s in 𝓝 (0 : ℂ),
      ‖(Ψ (G.coeff i)).eval s‖ < ‖(Ψ (G.coeff i)).eval 0‖ + 1 := fun i =>
    ((Ψ (G.coeff i)).continuous.norm.tendsto 0).eventually (gt_mem_nhds (lt_add_one _))
  refine ⟨∑ i ∈ Finset.range G.natDegree, (‖(Ψ (G.coeff i)).eval 0‖ + 1) + 1, ?_⟩
  filter_upwards [(Finset.range G.natDegree).eventually_all.2 fun i _ => h1 i] with s hs φ hφ
  have hm : (G.map ((evalRingHom s).comp Ψ)).Monic := hG.map _
  have hr : (G.map ((evalRingHom s).comp Ψ)).IsRoot (φ b) := by
    rw [IsRoot, eval_map, ← hφ, ← hom_eval₂, hGb, map_zero]
  have h2 := hr.norm_lt_cauchyBound hm.ne_zero
  rw [cauchyBound, hm.leadingCoeff, nnnorm_one, div_one, hG.natDegree_map] at h2
  have h3 : ((Finset.range G.natDegree).sup
      (fun i => ‖(G.map ((evalRingHom s).comp Ψ)).coeff i‖₊) : NNReal) ≤
      ∑ i ∈ Finset.range G.natDegree, (‖(Ψ (G.coeff i)).eval 0‖₊ + 1) := by
    refine Finset.sup_le fun i hi => ?_
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun i => ‖(Ψ (G.coeff i)).eval 0‖₊ + 1) (fun _ _ => zero_le) hi)
    rw [coeff_map]
    exact_mod_cast (hs i hi).le
  have h4 := h2.le.trans (add_le_add_left h3 1)
  have h5 := NNReal.coe_le_coe.2 h4
  push_cast at h5
  exact h5
end GlobalTheory.SmallPoint
