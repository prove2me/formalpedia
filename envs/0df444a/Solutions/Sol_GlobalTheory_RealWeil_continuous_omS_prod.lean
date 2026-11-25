-- Prove2me | solution 1 for GlobalTheory.RealWeil.continuous_omS_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:14:44.294235+00:00
-- url     : https://prove2.me/submissions/7d0aa9ae-87bb-4540-8afc-9c81c399c3c4

import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousMetaplecticSchwartzActionProd
import Theorems.Thm_GlobalTheory_IsSiegel_smul
import Theorems.Thm_GlobalTheory_RealWeil_exists_seminorm_le
import Theorems.Thm_GlobalTheory_RealWeil_schwartzToL2_apply
import Theorems.Thm_GlobalTheory_RealWeil_toLp_dRho_omS
import Theorems.Thm_GlobalTheory_RealWeil_weylAlg_induction


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.RealWeil
namespace GlobalTheory.RealWeil
theorem _root_.solution (l : Type) [Fintype l] [DecidableEq l] (G : Type) [Group G] [TopologicalSpace G]
    (pr : G →* Matrix.symplecticGroup l ℝ) (om : G →* (L2 l ≃ₗᵢ[ℂ] L2 l)) (omS : G →* (Sch l →L[ℂ] Sch l))
    (hpr : Continuous pr) (hom : ∀ f : L2 l, Continuous fun g => om g f)
    (h3 : ∀ (g : G) (w : l ⊕ l → ℝ) (f : L2 l),
      om g (rho w f) = rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f))
    (h4 : ∀ (g : G) (f : Sch l), om g (f.toLp 2) = (omS g f).toLp 2) :
    Continuous fun x : G × Sch l => omS x.1 x.2 := by

  have hjoint : Continuous fun x : G × L2 l => om x.1 x.2 :=
    continuous_prod_of_continuous_lipschitzWith' (fun x : G × L2 l => om x.1 x.2) 1
      (fun g => (om g).isometry.lipschitz) hom
  have hentry : ∀ a b, Continuous fun g => (pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) a b := fun a b =>
    by
    have hv : Continuous fun g => (pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) :=
      (continuous_subtype_val (p := fun M => M ∈ Matrix.symplecticGroup l ℝ)).comp hpr
    exact (continuous_apply b).comp ((continuous_apply a).comp hv)

  have key : ∀ {A : Sch l →L[ℂ] Sch l}, A ∈ weylAlg l →
      Continuous fun x : G × Sch l => schwartzToL2 l (A (omS x.1 x.2)) := by
    intro A hA
    refine weylAlg_induction (P := fun A => Continuous fun x : G × Sch l => schwartzToL2 l (A (omS x.1 x.2)))
      ?_ ?_ ?_ ?_ ?_ hA
    · have e : (fun x : G × Sch l => schwartzToL2 l ((1 : Sch l →L[ℂ] Sch l) (omS x.1 x.2))) =
          fun x => om x.1 (schwartzToL2 l x.2) := by
        funext x
        simp only [ContinuousLinearMap.one_apply, schwartzToL2_apply, h4]
      rw [e]
      exact hjoint.comp (continuous_fst.prodMk ((schwartzToL2 l).continuous.comp continuous_snd))
    · intro A w ih
      simp only [toLp_dRho_omS h3 h4]
      refine continuous_finset_sum _ fun a _ => ?_
      have hih : Continuous fun x : G × Sch l => schwartzToL2 l (A (omS x.1 (dRho (Pi.single a 1) x.2))) :=
        ih.comp (continuous_fst.prodMk ((dRho (Pi.single a 1)).continuous.comp continuous_snd))
      refine Continuous.smul (M := ℂ) ?_ hih
      refine continuous_ofReal.comp ?_
      simp only [mulVec, dotProduct, Matrix.neg_apply, Matrix.mul_apply, transpose_apply]
      exact continuous_finset_sum _ fun b _ => Continuous.mul (Continuous.neg (continuous_finset_sum _ fun c _ =>
        Continuous.mul (continuous_finset_sum _ fun d _ => continuous_const.mul
          ((hentry _ _).comp continuous_fst)) continuous_const)) continuous_const
    · simp only [ContinuousLinearMap.zero_apply, map_zero]
      exact continuous_const
    · intro A B hA hB
      simp only [ContinuousLinearMap.add_apply, map_add]
      exact hA.add hB
    · intro c A hA
      simp only [ContinuousLinearMap.smul_apply, map_smul]
      exact hA.const_smul c
  rw [continuous_iff_continuousAt]
  intro x0
  unfold ContinuousAt
  rw [(schwartz_withSeminorms ℂ (EuclideanSpace ℝ l) ℂ).tendsto_nhds]
  rintro ⟨k, n⟩ ε hε
  obtain ⟨A, hA, hb⟩ := exists_seminorm_le (l := l) k n
  have ht : Filter.Tendsto (fun x : G × Sch l => ∑ r, ‖schwartzToL2 l (A r (omS x.1 x.2)) - schwartzToL2 l (A r (omS x0.1 x0.2))‖)
      (nhds x0) (nhds 0) := by
    have : (0 : ℝ) = ∑ r : Fin n → l, ‖schwartzToL2 l (A r (omS x0.1 x0.2)) - schwartzToL2 l (A r (omS x0.1 x0.2))‖ := by simp
    rw [this]
    exact tendsto_finset_sum _ fun r _ => ((((key (hA r)).sub continuous_const).norm).tendsto x0)
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with x hx
  refine lt_of_le_of_lt ?_ hx
  rw [SchwartzMap.schwartzSeminormFamily_apply]
  refine (hb _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← schwartzToL2_apply, map_sub, map_sub]
end GlobalTheory.RealWeil
