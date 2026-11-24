-- Prove2me | solution 1 for GlobalTheory.firstJet_eq_aug_add_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:10:04.74587+00:00
-- url     : https://prove2.me/submissions/1ae91639-2802-43a1-a5eb-b990ab051674

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LawsChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FirstJetEqProdTangent
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map
import Theorems.Thm_GlobalTheory_SqZero_ker_fst_sq
import Theorems.Thm_GlobalTheory_SqZero_mul_eq_zero_of_sq
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_GlobalTheory_SqZero_vecTo_apply
import Theorems.Thm_GlobalTheory_SqZero_vecTo_single
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetLift_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_zR_mem_ker
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open SqZero TrivSqZeroExt
namespace GlobalTheory
theorem _root_.solution {R : Type} [CommRing R] {d : ℕ} (a : JetR R (Fin d) 1) :
    a = algebraMap R _ (jetAug R (Fin d) 1 a) +
      ∑ j, algebraMap R _ (dualLift (Pi.single j (1 : R)) a).snd * zR 1 j := by
  let Φ : JetR R (Fin d) 1 →ₐ[R] TrivSqZeroExt R (Fin d → R) :=
    jetLift R (RingHom.ker (fstHom R R (Fin d → R))) (ker_fst_sq _)
      (fun j => inr (Pi.single j 1)) (fun _ => (RingHom.mem_ker).mpr rfl)
  have hΦ : ∀ j, Φ (zR 1 j) = inr (Pi.single j 1) := fun j => jetLift_zR _ _ _ _ j
  have hz : ∀ i j : Fin d, zR (R := R) 1 i * zR 1 j = 0 := fun i j =>
    mul_eq_zero_of_sq (ker_jetAug_pow (R := R) (Fin d) 1) (zR_mem_ker 1 i) (zR_mem_ker 1 j)
  have h₁ : (vecTo (Algebra.ofId R _) (zR 1) hz).comp Φ = AlgHom.id R _ :=
    jet_ext fun j => by rw [AlgHom.comp_apply, hΦ, vecTo_single, AlgHom.id_apply]
  have h₂ : (fstHom R R (Fin d → R)).comp Φ = jetAug R (Fin d) 1 :=
    jet_ext fun j => by rw [AlgHom.comp_apply, hΦ, jetAug_zR]; rfl
  have h₃ : ∀ j, (TrivSqZeroExt.map (LinearMap.proj j : (Fin d → R) →ₗ[R] R)).comp Φ =
      dualLift (Pi.single j (1 : R)) := fun j => jet_ext fun i => by
    rw [AlgHom.comp_apply, hΦ, dualLift_zR, map_inr, LinearMap.proj_apply, Pi.single_apply,
      Pi.single_apply]
    simp only [eq_comm]
  conv_lhs => rw [← AlgHom.id_apply (R := R) a, ← h₁, AlgHom.comp_apply, vecTo_apply]
  simp only [← h₂, ← h₃, AlgHom.comp_apply, snd_map, LinearMap.proj_apply]
  rfl
end GlobalTheory
