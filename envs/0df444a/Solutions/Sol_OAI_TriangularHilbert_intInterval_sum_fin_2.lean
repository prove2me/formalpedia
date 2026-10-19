-- Prove2me | solution 2 for OAI.TriangularHilbert.intInterval_sum_fin
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T04:34:46.616867+00:00
-- url     : https://prove2.me/submissions/290f4c51-1c77-4fb7-8d13-2441cbfc9b7f

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/GaussianMax.lean:L25-L42
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.intInterval_sum_fin. The node keeps its source
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

-- ---- from OAI.Analysis.TriangularHilbert.IntWeak ----
namespace OAI

section
namespace TriangularHilbert
open scoped BigOperators
noncomputable section

lemma mem_intInterval (m n : ℤ) (r : ℕ) :
    m ∈ intInterval n r ↔ n-(r:ℤ) ≤ m ∧ m ≤ n+r := Finset.mem_Icc

end
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.GaussianMax ----
namespace OAI

section
namespace TriangularHilbert
open scoped BigOperators
noncomputable section

lemma intInterval_sum_fin (n : ℤ) (N : ℕ) (f : ℤ → ℝ) :
    (∑ m ∈ intInterval n N, f m) = ∑ i : Fin (2*N+1), f (n-(N:ℤ)+(i:ℕ)) := by
  symm
  apply Finset.sum_bij (fun (i : Fin (2*N+1)) _ => n-(N:ℤ)+(i:ℕ))
  · intro i _
    rw [mem_intInterval]
    have hi := i.isLt
    constructor <;> omega
  · intro i _ j _ he
    apply Fin.ext
    omega
  · intro m hm
    rw [mem_intInterval] at hm
    refine ⟨⟨(m-(n-(N:ℤ))).toNat,by omega⟩,Finset.mem_univ _,?_⟩
    dsimp
    omega
  · intro i _
    rfl

end
end TriangularHilbert
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TriangularHilbert.intInterval_sum_fin := @_root_.OAI.TriangularHilbert.intInterval_sum_fin
