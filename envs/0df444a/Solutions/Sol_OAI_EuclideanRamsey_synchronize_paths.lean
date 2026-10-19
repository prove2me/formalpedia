-- Prove2me | solution 1 for OAI.EuclideanRamsey.synchronize_paths
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:58:49.4858+00:00
-- url     : https://prove2.me/submissions/2206852d-5927-460f-b26e-3e4ea25aa81f

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/PathSynchronization.lean:L105-L131
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.synchronize_paths. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SignedRows
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathFractions
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DerivedFractions
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathWords
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_UltrafilterStrings
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathSynchronization
import Theorems.Thm_OAI_EuclideanRamsey_synchronized_chain

-- ---- from OAI.Combinatorics.EuclideanRamsey.PathSynchronization ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
namespace OAI

universe uIndex uAlpha

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace
open Filter

namespace EuclideanRamsey
open scoped BigOperators
variable {ι : Type uIndex} {a : ι → FiniteEuclidean}

lemma Path.scale {w lmb} (h : Path a w lmb) (c : ℝ) (hc : 0 ≤ c) :
    Path a (fun i => scaleGroup c (w i)) (c*lmb) := by
  induction h with
  | diag g => simpa using (Path.diag (a:=a) (scaleGroup c g))
  | @copy u b hb =>
    have hcopy : CopyPath a (c*u) (fun i => Real.sqrt c • b i) := by
      refine ⟨mul_nonneg hc hb.1,?_⟩
      intro i j
      rw [← smul_sub,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,Real.sq_sqrt hc,hb.2]
      ring
    simpa only [scaleGroup,FreeGroup.map.of] using Path.copy _ hcopy
  | mul _ _ ihu ihv => simpa only [map_mul,Pi.mul_apply,Pi.mul_def,mul_add] using ihu.mul ihv

theorem synchronize_paths (n : ℕ) (hn : 1 ≤ n) {w : ι → LetterGroup} {lmb μ : ℝ}
    (hp : Path a w lmb) (hm : Path a w μ) (hlmb : 0 < lmb)
    (hratio : μ/lmb < 1/(n:ℝ)) :
    ∃ W,∀ t : ℕ,1 ≤ t → t ≤ n → Path a W (1/(t:ℝ)) := by
  let ρ := μ/lmb
  have hn' : (0:ℝ)<n := Nat.cast_pos.mpr (by omega)
  have hρ : ρ<1 := lt_of_lt_of_le hratio (by exact (div_le_one hn').mpr (by exact_mod_cast hn))
  have hnorm : Path a (fun i => scaleGroup lmb⁻¹ (w i)) 1 := by
    simpa [inv_mul_cancel₀ hlmb.ne'] using hp.scale lmb⁻¹ (inv_nonneg.mpr hlmb.le)
  have hnorm' : Path a (fun i => scaleGroup lmb⁻¹ (w i)) ρ := by
    simpa [ρ,div_eq_mul_inv,mul_comm] using hm.scale lmb⁻¹ (inv_nonneg.mpr hlmb.le)
  let v (j : ℕ) : ℝ := if j<n then 1/(j+1:ℕ) else ρ
  obtain ⟨W,hW⟩ := synchronized_chain hnorm hnorm' hρ v n (by simp [v]; omega)
    (by simp [v]) (by
      intro j hj
      dsimp [v]
      rw [ite_eq_left hj]
      split_ifs with hj'
      · apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast (by omega : j+1≤j+1+1)
      · have he : j+1=n := by omega
        simpa [he,ρ] using hratio.le)
  refine ⟨W,?_⟩
  intro t ht htn
  have ht0 : t-1<n := by omega
  have h := hW (t-1) (by omega)
  simpa only [v,ite_eq_left ht0,show t-1+1=t by omega] using h
end EuclideanRamsey

end

end OAI

-- ---- platform node ----
open OAI OAI.EuclideanRamsey
open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace
open Filter
open scoped BigOperators


theorem solution.{uIndex} : type_of% @_root_.OAI.EuclideanRamsey.synchronize_paths.{uIndex} := @_root_.OAI.EuclideanRamsey.synchronize_paths.{uIndex}
