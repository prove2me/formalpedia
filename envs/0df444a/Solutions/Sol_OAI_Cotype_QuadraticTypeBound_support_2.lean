-- Prove2me | solution 2 for OAI.Cotype.QuadraticTypeBound.support
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:24:08.972198+00:00
-- url     : https://prove2.me/submissions/a247e628-79e3-411d-9540-cdb51396767b

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/IndependentSigns.lean:L76-L96
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.QuadraticTypeBound.support. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
import Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse
import Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral
import Definitions.Def_OAI_Analysis_Cotype_ProjectionResolvent
import Definitions.Def_OAI_Analysis_Cotype_SectorResolvent
import Definitions.Def_OAI_Analysis_Cotype_FiniteContour
import Definitions.Def_OAI_Analysis_Cotype_NoiseHypercontractivity
import Definitions.Def_OAI_Analysis_Cotype_QuadraticTypeTensor
import Theorems.Thm_OAI_Cotype_sum_norm_sq_extend

-- ---- from OAI.Analysis.Cotype.WalshCoordinates ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem average_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → X) : average (fun a => f (e a)) = average f := by
  simp only [average, Fintype.card_congr e, Equiv.sum_comp]

theorem average_comm {α β : Type*} [Fintype α] [Fintype β] (f : α → β → X) :
    average (fun a => average (f a)) = average (fun b => average (fun a => f a b)) := by
  simp only [average, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp [mul_comm]

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.QuadraticTypeTensor ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem average_const_value {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    average (fun _ : α => c) = c := by
  simp [average,smul_eq_mul]

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.IndependentSigns ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem average_comp_coordinate_embedding {n m : ℕ} (j : Fin n ↪ Fin m)
    (f : Cube n → ℝ) :
    average (fun ζ : Cube m => f (fun i => ζ (j i))) = average f := by
  classical
  let F : Cube m → Cube n → ℝ := fun ζ ε => f (fun i => xor (ζ (j i)) (ε i))
  have hrow (ζ : Cube m) : average (F ζ) = average f := by
    exact average_equiv (signCubeTwist (fun i => ζ (j i))) f
  have hcol (ε : Cube n) : average (fun ζ => F ζ ε) =
      average (fun ζ : Cube m => f (fun i => ζ (j i))) := by
    let σ : Cube m := Function.extend j ε (fun _ => false)
    have hσ i : σ (j i) = ε i := j.injective.extend_apply _ _ _
    have hh := average_equiv (signCubeTwist σ) (fun ζ : Cube m => f (fun i => ζ (j i)))
    simpa only [F,signCubeTwist,Equiv.coe_fn_mk,hσ,Bool.xor_comm] using hh
  calc
    _ = average (fun ε : Cube n => average (fun ζ : Cube m => F ζ ε)) := by
      simp only [hcol,average_const_value]
    _ = average (fun ζ : Cube m => average (F ζ)) := average_comm _
    _ = average f := by simp only [hrow,average_const_value]

theorem rademacherSum_extend {n m : ℕ} (j : Fin n ↪ Fin m) (x : Fin n → X)
    (ζ : Cube m) :
    rademacherSum X (Function.extend j x (fun _ => 0)) ζ =
      rademacherSum X x (fun i => ζ (j i)) := by
  classical
  let y : Fin m → X := Function.extend j x (fun _ => 0)
  have hy i : y (j i) = x i := j.injective.extend_apply _ _ _
  have hz u (hu : u ∉ Finset.univ.image j) : y u = 0 := by
    apply Function.extend_apply'
    simpa using hu
  change (∑ u, sign (ζ u) • y u) = ∑ i, sign (ζ (j i)) • x i
  calc
    _ = ∑ u ∈ Finset.univ.image j, sign (ζ u) • y u :=
      (Finset.sum_subset (Finset.subset_univ _) (fun u _ hu => by rw [hz u hu,smul_zero])).symm
    _ = _ := by rw [Finset.sum_image (fun _ _ _ _ he => j.injective he)]; simp only [hy]

theorem rademacher_sq_extend {n m : ℕ} (j : Fin n ↪ Fin m) (x : Fin n → X) :
    cubeL2 X (rademacherSum X (Function.extend j x (fun _ => 0)))^2 =
      cubeL2 X (rademacherSum X x)^2 := by
  simp only [cubeL2_sq,rademacherSum_extend]
  exact average_comp_coordinate_embedding j (fun ε => ‖rademacherSum X x ε‖^2)

theorem QuadraticTypeBound.mono_dim {n m : ℕ} {A : ℝ}
    (h : QuadraticTypeBound X m A) (hnm : n ≤ m) : QuadraticTypeBound X n A := by
  intro x
  have hh := h (Function.extend (Fin.castLEEmb hnm) x (fun _ => 0))
  simpa only [rademacher_sq_extend,sum_norm_sq_extend] using hh

theorem QuadraticTypeBound.support {m N : ℕ} {A : ℝ}
    (h : QuadraticTypeBound X m A) (s : Finset (Fin N)) (hs : s.card ≤ m)
    (x : Fin N → X) (hx : ∀ i, i ∉ s → x i = 0) :
    cubeL2 X (rademacherSum X x)^2 ≤ A*∑ i, ‖x i‖^2 := by
  classical
  let e : Fin s.card ≃ s := by simpa using (Fintype.equivFin s).symm
  let j : Fin s.card ↪ Fin N := e.toEmbedding.trans (Function.Embedding.subtype (fun i => i ∈ s))
  let y : Fin s.card → X := fun i => x (j i)
  have he : Function.extend j y (fun _ => 0) = x := by
    funext i
    by_cases hi : i ∈ s
    · obtain ⟨k,hk⟩ := e.surjective ⟨i,hi⟩
      have hj : j k = i := congrArg Subtype.val hk
      rw [← hj,j.injective.extend_apply]
    · have hz : ¬ ∃ k, j k = i := by
        rintro ⟨k,hk⟩
        exact hi (hk ▸ (e k).property)
      rw [Function.extend_apply' _ _ _ hz,hx i hi]
  have hh := h.mono_dim hs y
  rw [← rademacher_sq_extend j y,← sum_norm_sq_extend j y,he] at hh
  exact hh

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.QuadraticTypeBound.support := @_root_.OAI.Cotype.QuadraticTypeBound.support
