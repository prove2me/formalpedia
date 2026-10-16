-- Prove2me | solution 1 for OAI.PermanentBorder.HasBorderDeterminant.coefficientwise_limit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:42:09.664982+00:00
-- url     : https://prove2.me/submissions/fe3ac19c-78df-4c93-a70c-67cc72426660

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/BorderClosure.lean:L11-L49
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.HasBorderDeterminant.coefficientwise_limit. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts
import Definitions.Def_OAI_Algebra_Determinantal_SchurDifferentials
import Definitions.Def_OAI_Algebra_Determinantal_SchurLifts
import Definitions.Def_OAI_Algebra_Determinantal_BilinearCounts
import Definitions.Def_OAI_Algebra_Determinantal_RegularSections
import Definitions.Def_OAI_Algebra_Determinantal_SmoothSlices
import Definitions.Def_OAI_Algebra_Determinantal_SliceCertificates
import Definitions.Def_OAI_Algebra_Determinantal_GenericPolars
import Definitions.Def_OAI_Algebra_Determinantal_RankTransfer
import Definitions.Def_OAI_Algebra_Determinantal_Model

-- ---- from OAI.Algebra.Determinantal.BorderClosure ----
namespace OAI

namespace PermanentBorder

open Filter
open scoped Topology

/-- Fixed-size border representations are closed under sequential coefficientwise
limits. The approximating matrices remain arbitrary complex affine matrices of
exactly the original size; no uniform rate or coefficient bound is assumed. -/
theorem HasBorderDeterminant.coefficientwise_limit
    {σ : Type*} [Fintype σ] {n : ℕ} {P : ℕ → Poly σ} {p : Poly σ}
    (hP : ∀ j, HasBorderDeterminant n (P j))
    (hp : ∀ d : σ →₀ ℕ,
      Tendsto (fun j => (P j).coeff d) atTop (𝓝 (p.coeff d))) :
    HasBorderDeterminant n p := by
  classical
  let Coeff := (σ →₀ ℕ) → ℂ
  let MatData := Matrix (Fin n) (Fin n) ℂ ×
    (σ → Matrix (Fin n) (Fin n) ℂ)
  let coefficients : MatData → Coeff := fun B d =>
    (affineMatrixPolynomial n B.1 B.2).coeff d
  let S : Set Coeff := Set.range coefficients
  have hmem : ∀ j, (fun d => (P j).coeff d) ∈ closure S := by
    intro j
    obtain ⟨_, A₀, A, hA⟩ := hP j
    apply mem_closure_iff_seq_limit.mpr
    refine ⟨fun k => coefficients (A₀ k, A k), ?_, ?_⟩
    · intro k
      exact ⟨(A₀ k, A k), rfl⟩
    · exact tendsto_pi_nhds.mpr hA
  have hclosed : (fun d => p.coeff d) ∈ closure S :=
    isClosed_closure.mem_of_tendsto (tendsto_pi_nhds.mpr hp)
      (Filter.Eventually.of_forall hmem)
  obtain ⟨Q, hQ, hlim⟩ := mem_closure_iff_seq_limit.mp hclosed
  have hchoose : ∀ j, ∃ B : MatData, coefficients B = Q j := hQ
  choose B hB using hchoose
  refine ⟨(hP 0).1, (fun j => (B j).1), (fun j => (B j).2), ?_⟩
  intro d
  have he :
      (fun j => (affineMatrixPolynomial n (B j).1 (B j).2).coeff d) =
      (fun j => Q j d) := by
    funext j
    exact congrFun (hB j) d
  rw [he]
  exact tendsto_pi_nhds.mp hlim d

end PermanentBorder

end OAI

-- ---- platform node ----
open OAI OAI.PermanentBorder
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.PermanentBorder.HasBorderDeterminant.coefficientwise_limit := @_root_.OAI.PermanentBorder.HasBorderDeterminant.coefficientwise_limit
