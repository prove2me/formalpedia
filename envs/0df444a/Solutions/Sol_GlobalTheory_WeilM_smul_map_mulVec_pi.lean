-- Prove2me | solution 1 for GlobalTheory.WeilM.smul_map_mulVec_pi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:28.441971+00:00
-- url     : https://prove2.me/submissions/89558a26-98f2-46ad-9aad-ec16493955c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormPowTwoPowSubOneGe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ValuativeRel
open scoped NNReal Topology Pointwise
open GlobalTheory GlobalTheory.WeilM
variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {F} [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]
  {κ : Type} [Fintype κ] [DecidableEq κ]
namespace GlobalTheory.WeilM
theorem _root_.solution (M : Matrix κ κ F) (u : Fˣ) (hu : (u : F) = M.det) :
    (distribHaarChar F u : ENNReal) • Measure.map M.mulVec (Measure.pi fun _ : κ => ν) = Measure.pi fun _ : κ => ν := by
  haveI := SplitWeil.secondCountable F
  haveI := SplitWeil.t2Space F
  have hm : ∀ A : Matrix κ κ F, Measurable A.mulVec := fun A =>
    (continuous_const.matrix_mulVec continuous_id).measurable
  have hM : M.det ≠ 0 := hu ▸ u.ne_zero
  revert u
  apply diagonal_transvection_induction_of_det_ne_zero _ M hM
  · intro D hD u hu
    refine (Measure.pi_eq fun s hs => ?_).symm
    rw [det_diagonal] at hD hu
    have A : ∀ i, D i ≠ 0 := fun i => Finset.prod_ne_zero_iff.1 hD i (Finset.mem_univ i)
    have hu' : u = ∏ i, Units.mk0 (D i) (A i) := Units.ext (by simp [hu])
    rw [Measure.smul_apply, Measure.map_apply (hm _) (MeasurableSet.univ_pi hs)]
    have : ((diagonal D).mulVec ⁻¹' Set.pi Set.univ fun i : κ => s i) =
        Set.pi Set.univ fun i : κ => (Units.mk0 (D i) (A i))⁻¹ • s i := by
      ext f
      simp only [Set.mem_preimage, Set.mem_univ_pi, mulVec_diagonal]
      exact forall_congr' fun i => (Set.mem_inv_smul_set_iff (a := Units.mk0 (D i) (A i))).symm
    rw [this, Measure.pi_pi, hu', map_prod, ENNReal.coe_finset_prod, smul_eq_mul, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [distribHaarChar_mul, smul_inv_smul]
  · intro t u hu
    have hu' : u = 1 := Units.ext (by simp [hu])
    rw [hu', map_one, ENNReal.coe_one, one_smul]
    refine (Measure.pi_eq fun s hs ↦ ?_).symm
    have h2s : MeasurableSet (Set.univ.pi s) := .pi Set.countable_univ fun i _ ↦ hs i
    simp_rw [← Measure.pi_pi, ← lintegral_indicator_one h2s]
    rw [lintegral_map (measurable_one.indicator h2s) (hm _)]
    refine lintegral_eq_of_lmarginal_eq {t.i} ((measurable_one.indicator h2s).comp (hm _))
      (measurable_one.indicator h2s) ?_
    simp_rw [lmarginal_singleton]
    ext x
    cases t with | mk t_i t_j t_hij t_c =>
    simp [transvection, add_mulVec, single_mulVec, t_hij.symm, ← Function.update_add,
      lintegral_add_right_eq_self fun xᵢ ↦ Set.indicator (Set.univ.pi s) 1 (Function.update x t_i xᵢ)]
  · intro A B hA hB IHA IHB u hu
    have hu' : u = Units.mk0 _ hA * Units.mk0 _ hB := Units.ext (by simp [hu])
    have e : (A * B).mulVec = A.mulVec ∘ B.mulVec := funext fun x => (mulVec_mulVec x A B).symm
    rw [hu', map_mul, ENNReal.coe_mul, mul_smul, e, ← Measure.map_map (hm _) (hm _), ← Measure.map_smul,
      IHB _ rfl, IHA _ rfl]
end GlobalTheory.WeilM
