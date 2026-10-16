-- Prove2me | solution 1 for OAI.QuantumTrace.cfc_apply_eigenvector
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:08:23.817831+00:00
-- url     : https://prove2.me/submissions/8a090d21-858e-44e3-ac95-5aecb80f3ec6

-- Generated from openai/math@1581d4c lean/OAI/Analysis/QuantumTrace/Basic.lean:L306-L340
-- (upload_full_project.md Phase 4): solution for node OAI.QuantumTrace.cfc_apply_eigenvector. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic

-- ---- from OAI.Analysis.QuantumTrace.Basic ----
-- Lean 4.34 name (arguments swapped) of CStarAlgebra.norm_le_norm_of_nonneg_of_le in Mathlib 0df444a.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory

namespace QuantumTrace

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι κ : Type*}

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*}

end

section
open Filter

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {ι : Type*}

end

section
open Filter ContinuousLinearMap InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {ι : Type*}

end

section
open ContinuousLinearMap Module.End Submodule
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*}

end

section
open ContinuousLinearMap Module.End
open scoped ContinuousFunctionalCalculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem cfc_apply_eigenvector {T : E →L[ℂ] E} (hs : T.IsSymmetric)
    {x : E} {μ : ℂ} (he : T x = μ • x) (f : ℂ → ℂ)
    (hf : ContinuousOn f (spectrum ℂ T)) : cfc f T x = f μ • x := by
  by_cases hx : x = 0
  · simp [hx]
  have hev : HasEigenvalue T.toLinearMap μ :=
    hasEigenvalue_of_hasEigenvector ⟨mem_eigenspace_iff.mpr he, hx⟩
  have hm : μ ∈ spectrum ℂ T := by
    rw [ContinuousLinearMap.spectrum_eq]
    exact hev.mem_spectrum
  have hr := hs.conj_eigenvalue_eq_self hev
  have allf (g : C(spectrum ℂ T, ℂ)) :
      cfcHom hs.isSelfAdjoint.isStarNormal g x = g ⟨μ, hm⟩ • x := by
    induction g using ContinuousMap.induction_on_of_compact with
    | const r =>
      change cfcHom hs.isSelfAdjoint.isStarNormal (algebraMap ℂ C(spectrum ℂ T, ℂ) r) x = r • x
      rw [AlgHomClass.commutes]
      rfl
    | id => simpa only [cfcHom_id, ContinuousMap.restrict_apply, ContinuousMap.id_apply] using he
    | star_id =>
      rw [map_star, cfcHom_id, hs.isSelfAdjoint.star_eq]
      simpa [hr] using he
    | add g h hg hh => simp [map_add, hg, hh, add_smul]
    | mul g h hg hh =>
      simp only [map_mul, mul_apply_eq_comp, hh, map_smul, hg,
        ContinuousMap.mul_apply, mul_smul]
      exact smul_comm _ _ _
    | frequently g hg =>
      have hc : IsClosed {g : C(spectrum ℂ T, ℂ) |
          cfcHom hs.isSelfAdjoint.isStarNormal g x = g ⟨μ, hm⟩ • x} :=
        isClosed_eq ((cfcHom_continuous _).clm_apply continuous_const)
          ((continuous_eval_const _).smul continuous_const)
      exact hc.closure_eq.le hg.mem_closure
  rw [cfc_apply f T hs.isSelfAdjoint.isStarNormal hf]
  exact allf ⟨_, hf.domRestrict⟩

end

section

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι κ : Type*}

end

section

variable {ι : Type*}

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*}

end

section

open Filter Topology
open scoped Classical
variable {ι : Type*}
end

section
open Filter Topology
open scoped Classical
variable {ι : Type*}

end

section
open Filter Topology
variable {ι : Type*}

end

section
open ContinuousLinearMap Module.End Submodule
universe v
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section
open Filter Topology
variable {ι : Type*}

end

section
open Filter Topology

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {ι : Type*}

end

section
variable {ι J : Type*}

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {J : Type*}

end

open scoped BigOperators ComplexConjugate
variable {E J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end QuantumTrace

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace QuantumTrace
variable {ι J : Type*}

end QuantumTrace

end

end OAI

-- ---- platform node ----
open OAI OAI.QuantumTrace
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open ContinuousLinearMap Module.End
open scoped ContinuousFunctionalCalculus


theorem solution : type_of% @_root_.OAI.QuantumTrace.cfc_apply_eigenvector := @_root_.OAI.QuantumTrace.cfc_apply_eigenvector
