-- Prove2me | solution 1 for GlobalTheory.AdLat.RootNear.inv_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:54:13.04098+00:00
-- url     : https://prove2.me/submissions/fe129652-bbd7-48d8-84b4-f1ba03c6b23a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIntegralUnitRootNormOneAdeleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsAdeleRingTensorEquivInfiniteProdFiniteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsRootNear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
noncomputable section
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.RootNear
namespace GlobalTheory.AdLat.RootNear
theorem _root_.solution {A R ι : Type} [CommRing A] [CommRing R] [Algebra A R] [TopologicalSpace A]
    [IsTopologicalRing A] [TopologicalSpace R] [IsModuleTopology A R] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A R) (i : A → A) (hi : ContinuousAt i 1) (hi1 : i 1 = 1)
    (hii : ∀ᶠ a in 𝓝 (1 : A), a * i a = 1) :
    ∀ V ∈ 𝓝 (1 : R), ∀ᶠ x in 𝓝 (1 : R), ∃ y ∈ V, x * y = 1 := by
  intro V hV
  have : ContinuousAdd R := IsModuleTopology.toContinuousAdd A R
  have hM : Continuous (fun x : R => Algebra.leftMulMatrix b x) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap
  have hb : Continuous (b.equivFun.symm) :=
    IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap
  let d : R → A := fun x => (Algebra.leftMulMatrix b x).det
  let adj : R → R := fun x => b.equivFun.symm ((Algebra.leftMulMatrix b x).adjugate *ᵥ b.equivFun 1)
  have hd : Continuous d := hM.matrix_det
  have hadj : Continuous adj := hb.comp (hM.matrix_adjugate.matrix_mulVec continuous_const)
  have hd1 : d 1 = 1 := by simp [d]
  have hadj1 : adj 1 = 1 := by simp [adj]
  have key : ∀ x, x * adj x = d x • (1 : R) := by
    intro x
    apply b.equivFun.injective
    have h1 : ∀ y : R, b.equivFun (x * y) = Algebra.leftMulMatrix b x *ᵥ b.equivFun y := by
      intro y
      have := Algebra.leftMulMatrix_mulVec_repr b x y
      simpa using this.symm
    rw [h1, map_smul]
    simp only [adj, d, LinearEquiv.apply_symm_apply, Matrix.mulVec_mulVec, Matrix.mul_adjugate,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  have hdt : Filter.Tendsto d (𝓝 1) (𝓝 1) := by
    have := hd.tendsto 1
    rwa [hd1] at this
  have hy : Filter.Tendsto (fun x => i (d x) • adj x) (𝓝 1) (𝓝 1) := by
    have h1 : Filter.Tendsto (fun x => i (d x)) (𝓝 1) (𝓝 1) := by
      have := hi.tendsto
      rw [hi1] at this
      exact this.comp hdt
    have h2 := h1.smul (hadj.tendsto 1)
    simpa [hadj1] using h2
  filter_upwards [hy hV, hdt hii] with x h1 h2
  refine ⟨_, h1, ?_⟩
  rw [mul_smul_comm, key, smul_smul, mul_comm, h2, one_smul]
end GlobalTheory.AdLat.RootNear
