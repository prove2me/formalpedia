-- Prove2me | solution 1 for OAI.GAD.spectralFactor_gram
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:08:23.459976+00:00
-- url     : https://prove2.me/submissions/4d53109c-47e1-4d86-b106-5bdab58cec76

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/StateEntropy.lean:L104-L119
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.spectralFactor_gram. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Pinching
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_GramMatrices
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ScalarDeficit
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ThermalEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_OutputConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_TensorEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PureRecursion
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_StateEntropy
import Theorems.Thm_OAI_GAD_spectral_pure_decomposition

-- ---- from OAI.InformationTheory.AmplitudeDamping.StateEntropy ----
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_1} {α : Type u_2} [Fintype ι] [DecidableEq ι] [Fintype α]

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_3} {α : Type u_4} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

theorem spectralFactor_gram {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    gram (spectralFactor hA) = A := by
  conv_rhs => rw [spectral_pure_decomposition hA.isHermitian]
  ext i j
  simp only [gram,Matrix.mul_apply,Matrix.conjTranspose_apply,spectralFactor,
    star_mul,Matrix.sum_apply,Matrix.smul_apply,pure,Complex.real_smul,
    Complex.star_def,Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro k _
  have hs : (Real.sqrt (hA.isHermitian.eigenvalues k) : ℂ)^2 =
      (hA.isHermitian.eigenvalues k : ℂ) := by exact_mod_cast Real.sq_sqrt (hA.eigenvalues_nonneg k)
  calc
    _ = (Real.sqrt (hA.isHermitian.eigenvalues k) : ℂ)^2 *
      (hA.isHermitian.eigenvectorUnitary i k * star (hA.isHermitian.eigenvectorUnitary j k)) := by
        simp only [Complex.star_def]; ring
    _ = _ := by rw [hs]; rfl

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix


theorem solution : type_of% @_root_.OAI.GAD.spectralFactor_gram := @_root_.OAI.GAD.spectralFactor_gram
