-- Prove2me | solution 2 for OAI.TriangularHilbert.sum_windowMask_variation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T04:47:16.065874+00:00
-- url     : https://prove2.me/submissions/5191558b-8ef0-4e36-9f2e-d3f44ea96aa1

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/Switch.lean:L49-L62
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.sum_windowMask_variation. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedTraceOrder
import Definitions.Def_OAI_Analysis_TriangularHilbert_MassPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedConvolution
import Definitions.Def_OAI_Analysis_TriangularHilbert_RankJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_ZeroStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_StarJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialAlgebra
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_TotalJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntWeak
import Definitions.Def_OAI_Analysis_TriangularHilbert_StrongLayer
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_FiniteLineMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_JumpScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_Switch

-- ---- from OAI.Analysis.TriangularHilbert.Switch ----
namespace OAI

section
namespace TriangularHilbert
open scoped BigOperators
noncomputable section

lemma windowMask_eq_sub (a b s : ℝ) (hab : a ≤ b) (A : ℂ) :
    windowMask a b s A = opening a s A-opening b s A := by
  unfold windowMask opening
  split_ifs <;> simp_all <;> linarith

lemma sum_opening_variation (t : ℕ → ℝ) (ht : Monotone t) (a : ℝ) (A : ℂ) (n : ℕ) :
    (∑ k ∈ Finset.range n, ‖opening a (t (k+1)) A-opening a (t k) A‖) =
      (if a ≤ t n then ‖A‖ else 0)-(if a ≤ t 0 then ‖A‖ else 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih]
    have hh := ht (Nat.le_succ n)
    have h0 := ht (Nat.zero_le n)
    unfold opening
    split_ifs <;> simp_all <;> linarith

lemma sum_windowMask_variation (t : ℕ → ℝ) (ht : Monotone t) (a b : ℝ) (hab : a ≤ b)
    (A : ℂ) (n : ℕ) :
    (∑ k ∈ Finset.range n, ‖windowMask a b (t (k+1)) A-windowMask a b (t k) A‖) ≤ 2*‖A‖ := by
  have hi := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range n) =>
    norm_sub_le (opening a (t (k+1)) A-opening a (t k) A)
      (opening b (t (k+1)) A-opening b (t k) A))
  have he (k : ℕ) : windowMask a b (t (k+1)) A-windowMask a b (t k) A =
      (opening a (t (k+1)) A-opening a (t k) A)-(opening b (t (k+1)) A-opening b (t k) A) := by
    rw [windowMask_eq_sub _ _ _ hab,windowMask_eq_sub _ _ _ hab]
    ring
  simp_rw [he]
  apply hi.trans
  rw [Finset.sum_add_distrib,sum_opening_variation t ht a A n,sum_opening_variation t ht b A n]
  split_ifs <;> linarith [norm_nonneg A]
end
end TriangularHilbert
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TriangularHilbert.sum_windowMask_variation := @_root_.OAI.TriangularHilbert.sum_windowMask_variation
