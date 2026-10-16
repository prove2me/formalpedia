-- Prove2me | solution 1 for OAI.Paper256.exists_smooth_kernel_extension
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:42:20.872085+00:00
-- url     : https://prove2.me/submissions/d2a49fa8-530b-480c-be7e-fd5152a81441

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/KernelLocal.lean:L14-L66
-- (upload_full_project.md Phase 4): solution for node OAI.Paper256.exists_smooth_kernel_extension. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_RawBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSpectrum
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitFrame
import Definitions.Def_OAI_Analysis_HyperbolicCones_CongruenceMaps
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockNormalization
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockReduction
import Definitions.Def_OAI_Analysis_HyperbolicCones_ScalingAlgebra
import Definitions.Def_OAI_Analysis_HyperbolicCones_FiniteTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilLimit
import Definitions.Def_OAI_Analysis_HyperbolicCones_Coordinates
import Definitions.Def_OAI_Analysis_HyperbolicCones_ConeMatrix
import Definitions.Def_OAI_Analysis_HyperbolicCones_GramProjection

-- ---- from OAI.Analysis.HyperbolicCones.GramProjection ----
namespace OAI

noncomputable section

open scoped ContDiff
open ContinuousLinearMap

universe u v w

namespace Paper256

section Gram

variable {E : Type u} {F : Type v} {W : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace E] [CompleteSpace F]

theorem gram_isUnit_of_injective [FiniteDimensional ℝ E]
    (T : E →L[ℝ] F) (hT : Function.Injective T) : IsUnit (T.adjoint.comp T) := by
  have hk : (T.adjoint.comp T).ker = ⊥ := by
    rw [T.ker_adjoint_comp_self]
    exact LinearMap.ker_eq_bot.mpr hT
  have hi : Function.Injective (T.adjoint.comp T) := LinearMap.ker_eq_bot.mp hk
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hi, LinearMap.surjective_of_injective hi⟩

theorem gramProjection_eq [FiniteDimensional ℝ F]
    (T : E →L[ℝ] F) (hT : IsUnit (T.adjoint.comp T)) :
    gramProjection T = T.range.starProjection := by
  ext y
  symm
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact ⟨Ring.inverse (T.adjoint.comp T) (T.adjoint y), rfl⟩
  · rw [T.orthogonal_range]
    change T.adjoint (y - T (Ring.inverse (T.adjoint.comp T) (T.adjoint y))) = 0
    rw [map_sub]
    change T.adjoint y - ((T.adjoint.comp T) * Ring.inverse (T.adjoint.comp T))
      (T.adjoint y) = 0
    rw [Ring.mul_inverse_cancel _ hT]
    simp

theorem one_sub_gramProjection_eq_kernel [FiniteDimensional ℝ F]
    (T : E →L[ℝ] F) (hT : IsUnit (T.adjoint.comp T))
    (A : F →L[ℝ] F) (hA : IsSelfAdjoint A) (hr : T.range = A.range) :
    1 - gramProjection T = A.ker.starProjection := by
  rw [gramProjection_eq T hT, hr]
  change ContinuousLinearMap.id ℝ F - A.range.starProjection = A.ker.starProjection
  rw [← Submodule.starProjection_orthogonal]
  simp only [A.orthogonal_range, hA.adjoint_eq]

theorem contDiffOn_gramProjection (T : W → E →L[ℝ] F) (U : Set W)
    (hT : ContDiffOn ℝ ∞ T U)
    (hu : ∀ x ∈ U, IsUnit ((T x).adjoint.comp (T x))) :
    ContDiffOn ℝ ∞ (fun x => gramProjection (T x)) U := by
  have hadj : ContDiff ℝ ∞ (fun A : E →L[ℝ] F => A.adjoint) :=
    (ContinuousLinearMap.adjoint : (E →L[ℝ] F) ≃ₗᵢ[ℝ] (F →L[ℝ] E)).contDiff
  have htadj : ContDiffOn ℝ ∞ (fun x => (T x).adjoint) U := hadj.comp_contDiffOn hT
  have hg := htadj.clm_comp hT
  have hi : ContDiffOn ℝ ∞ (fun x => Ring.inverse ((T x).adjoint.comp (T x))) U := by
    intro x hx
    exact ((contDiffAt_ringInverse ℝ (hu x hx).unit).congr_of_eventuallyEq
      (by exact Filter.Eventually.of_forall fun _ => rfl)).comp_contDiffWithinAt x
        (hg x hx)
  exact hT.clm_comp (hi.clm_comp htadj)

end Gram

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.KernelLocal ----
namespace OAI

noncomputable section

open scoped ContDiff RealInnerProductSpace
open Set ContinuousLinearMap

universe u v

namespace Paper256

theorem exists_smooth_kernel_extension
    {W : Type u} {F : Type v} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (S : Set W) (hne : S.Nonempty) (A : W → F →L[ℝ] F)
    (hA : ContDiff ℝ ∞ A) (hs : ∀ u ∈ S, IsSelfAdjoint (A u)) :
    ∃ v ∈ S, ∃ (U : Set W) (P : W → F →L[ℝ] F),
      IsOpen U ∧ v ∈ U ∧ ContDiffOn ℝ ∞ P U ∧
      ∀ u ∈ U, u ∈ S → P u = (A u).ker.starProjection := by
  let ranks : Set ℕ := (fun u => Module.finrank ℝ (A u).range) '' S
  have hfin : ranks.Finite := Set.finite_iff_bddAbove.mpr ⟨Module.finrank ℝ F, by
    rintro _ ⟨u, _, rfl⟩
    exact Submodule.finrank_le _⟩
  obtain ⟨r, hr, hmax⟩ := Set.exists_max_image ranks id hfin (hne.image _)
  obtain ⟨v, hv, rfl⟩ := hr
  let R : Submodule ℝ F := (A v).range
  let T : W → R →L[ℝ] F := fun u => (A u).comp R.subtypeL
  have hTv : Function.Injective (T v) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    change A v (x : F) = 0 at hx
    have hxo : (x : F) ∈ Rᗮ := by
      change (x : F) ∈ (A v).rangeᗮ
      rw [(A v).orthogonal_range, (hs v hv).adjoint_eq]
      exact hx
    apply Subtype.ext
    exact inner_self_eq_zero.mp (hxo x x.property)
  have ht : ContDiff ℝ ∞ T := hA.clm_comp contDiff_const
  have hadj : ContDiff ℝ ∞ (fun B : R →L[ℝ] F => B.adjoint) :=
    (ContinuousLinearMap.adjoint : (R →L[ℝ] F) ≃ₗᵢ[ℝ] (F →L[ℝ] R)).contDiff
  let G : W → R →L[ℝ] R := fun u => (T u).adjoint.comp (T u)
  have hg : ContDiff ℝ ∞ G := (hadj.comp ht).clm_comp ht
  let U : Set W := {u | IsUnit (G u)}
  have huopen : IsOpen U := by
    change IsOpen (G ⁻¹' {K : R →L[ℝ] R | IsUnit K})
    apply IsOpen.preimage hg.continuous
    exact Units.isOpen (R := R →L[ℝ] R)
  have hvu : v ∈ U := gram_isUnit_of_injective (T v) hTv
  refine ⟨v, hv, U, fun u => 1 - gramProjection (T u), huopen, hvu, ?_, ?_⟩
  · exact contDiffOn_const.sub (contDiffOn_gramProjection T U ht.contDiffOn (fun _ hu => hu))
  · intro u hu hus
    have hTu : Function.Injective (T u) := by
      have hGi := (ContinuousLinearMap.isUnit_iff_bijective.mp hu).1
      intro x y hxy
      apply hGi
      exact congrArg (T u).adjoint hxy
    have hrange : (T u).range = (A u).range := by
      apply Submodule.eq_of_le_of_finrank_le
      · rintro _ ⟨x, rfl⟩
        exact ⟨(x : F), rfl⟩
      · rw [LinearMap.finrank_range_of_inj hTu]
        exact hmax _ ⟨u, hus, rfl⟩
    exact one_sub_gramProjection_eq_kernel (T u) hu (A u) (hs u hus) hrange

end Paper256

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper256
open scoped ContDiff RealInnerProductSpace
open Set ContinuousLinearMap


theorem solution.{u,v} : type_of% @_root_.OAI.Paper256.exists_smooth_kernel_extension.{u,v} := @_root_.OAI.Paper256.exists_smooth_kernel_extension.{u,v}
