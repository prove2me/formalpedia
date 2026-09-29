-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.admissible_gl3CyclicSubspace_dualWhittakerFn3_rightTranslate
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/0768672d-4d15-5923-94ba-91c19f324df6

import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Theorems.Thm_LanglandsTunnell_CubicInduction_isGL3PsiWhittakerFn_dualWhittakerFn3
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Instances.Matrix
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_admissible_gl3CyclicSubspace_dualWhittakerFn3_rightTranslate

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors

namespace Ws46
namespace DUAL

open LanglandsTunnell LanglandsTunnell.CubicInduction

variable {F : Type*} [Field F]

theorem transposeInv3_mul (g h : GL (Fin 3) F) : transposeInv3 (g * h) = transposeInv3 g * transposeInv3 h := by
  apply Units.ext
  change Matrix.transpose (((g * h)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
    Matrix.transpose ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      Matrix.transpose ((h⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

theorem transposeInv3_transposeInv3 (g : GL (Fin 3) F) : transposeInv3 (transposeInv3 g) = g := by
  apply Units.ext
  change Matrix.transpose (Matrix.transpose ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) = _
  rw [Matrix.transpose_transpose]

def tI : GL (Fin 3) F →* GL (Fin 3) F where
  toFun := transposeInv3
  map_one' := by
    apply Units.ext
    change Matrix.transpose (((1 : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1
    rw [inv_one, Units.val_one, Matrix.transpose_one]
  map_mul' := transposeInv3_mul

@[scoped simp] theorem tI_apply (g : GL (Fin 3) F) : tI g = transposeInv3 g := rfl

theorem continuous_transposeInv3 [TopologicalSpace F] [IsTopologicalRing F] :
    Continuous (transposeInv3 : GL (Fin 3) F → GL (Fin 3) F) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Units.continuous_coe_inv.matrix_transpose :
      Continuous fun g : GL (Fin 3) F => Matrix.transpose ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
  · exact (Units.continuous_val.matrix_transpose :
      Continuous fun g : GL (Fin 3) F => Matrix.transpose ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))

def Lsub : (GL (Fin 3) F → ℂ) →ₗ[ℂ] (GL (Fin 3) F → ℂ) where
  toFun G := fun y => G (longWeyl3 * transposeInv3 y)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[scoped simp] theorem Lsub_apply (G : GL (Fin 3) F → ℂ) (y : GL (Fin 3) F) : Lsub G y = G (longWeyl3 * transposeInv3 y) := rfl

end Ws46.DUAL
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_admissible_gl3CyclicSubspace_dualWhittakerFn3_rightTranslate.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_admissible_gl3CyclicSubspace_dualWhittakerFn3_rightTranslate.Ws46.DUAL"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_admissible_gl3CyclicSubspace_dualWhittakerFn3_rightTranslate.Ws46"

open Ws46.DUAL LanglandsTunnell LanglandsTunnell.CubicInduction in
theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ))
    (W : LocalGL3 v → ℂ)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)))
    (g₃ : LocalGL3 v) :
    (∃ Ud : Subgroup (LocalGL3 v), IsOpen (Ud : Set (LocalGL3 v)) ∧
      ∀ k ∈ Ud, ∀ y : LocalGL3 v,
        dualWhittakerFn3 (fun x => W (x * g₃)) (y * k) = dualWhittakerFn3 (fun x => W (x * g₃)) y) ∧
    (∀ Ud : Subgroup (LocalGL3 v), IsOpen (Ud : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace (dualWhittakerFn3 (fun x => W (x * g₃))),
        (∀ k ∈ Ud, ∀ y : LocalGL3 v, F (y * k) = F y) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ))) ∧
    (∀ ψv : AddChar (v.adicCompletion ℚ) ℂ, IsGL3PsiWhittakerFn ψv W →
      IsGL3PsiWhittakerFn ψv⁻¹ (dualWhittakerFn3 (fun x => W (x * g₃)))) := by
  obtain ⟨Uv, hUo, hUinv⟩ := hsm
  classical

  set φ : LocalGL3 v →* LocalGL3 v := (MulAut.conj g₃⁻¹).toMonoidHom.comp tI with hφ
  have hφapply : ∀ k, φ k = g₃⁻¹ * transposeInv3 k * g₃ := fun k => by
    simp only [hφ, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, tI_apply,
      MulAut.conj_apply, inv_inv]
  have hφc : Continuous φ := by
    have : (φ : LocalGL3 v → LocalGL3 v) = fun k => g₃⁻¹ * transposeInv3 k * g₃ := funext hφapply
    rw [this]
    exact (continuous_const.mul continuous_transposeInv3).mul continuous_const
  refine ⟨⟨Uv.comap φ, hUo.preimage hφc, fun k hk y => ?_⟩, ?_, ?_⟩
  ·
    simp only [dualWhittakerFn3, transposeInv3_mul]
    have hk' : g₃⁻¹ * transposeInv3 k * g₃ ∈ Uv := by rw [← hφapply]; exact hk
    have := hUinv _ hk' (longWeyl3 * transposeInv3 y * g₃)
    rw [← this]
    congr 1
    group
  ·
    intro Ud hUd
    obtain ⟨B, hB⟩ := hadm (Ud.comap tI) (hUd.preimage continuous_transposeInv3)
    refine ⟨B.image Lsub, fun F hF hFinv => ?_⟩

    have hsub : gl3CyclicSubspace (dualWhittakerFn3 (fun x => W (x * g₃))) ≤ (gl3CyclicSubspace W).map Lsub := by
      unfold gl3CyclicSubspace
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨h, rfl⟩
      refine ⟨gl3AmbientRightTranslate (transposeInv3 h * g₃) W, Submodule.subset_span ⟨_, rfl⟩, ?_⟩
      funext y
      simp only [Lsub_apply, gl3AmbientRightTranslate_apply, dualWhittakerFn3, transposeInv3_mul, mul_assoc]
    obtain ⟨G, hG, rfl⟩ := Submodule.mem_map.mp (hsub hF)

    have hGinv : ∀ k ∈ Ud.comap tI, ∀ x : LocalGL3 v, G (x * k) = G x := by
      intro k hk x
      have h := hFinv (transposeInv3 k) hk (transposeInv3 (longWeyl3⁻¹ * x))
      simp only [Lsub_apply, transposeInv3_mul, transposeInv3_transposeInv3, mul_assoc, mul_inv_cancel_left] at h
      exact h
    have hGB := hB G hG hGinv
    rw [Finset.coe_image, ← Submodule.map_span]
    exact Submodule.mem_map_of_mem hGB
  ·
    intro ψv hW
    refine LanglandsTunnell.CubicInduction.isGL3PsiWhittakerFn_dualWhittakerFn3 ψv _ ?_
    intro x y z h
    show W (upperUnipotent3 x y z * h * g₃) = ψv (x + y) * W (h * g₃)
    rw [mul_assoc]
    exact hW x y z (h * g₃)

end S_LanglandsTunnell_CubicInduction_admissible_gl3CyclicSubspace_dualWhittakerFn3_rightTranslate
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_admissible_gl3CyclicSubspace_dualWhittakerFn3_rightTranslate (solution)
