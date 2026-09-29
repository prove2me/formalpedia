-- Prove2me | solution 1 for LT.LatticeTree.Vertex.isWithin_add_of_isWithin_of_isWithin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/ea23ce19-be4a-5b7c-a982-d3ad1951b552

import Definitions.Def_LatticeTreeBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LT_LatticeTree_Vertex_isWithin_add_of_isWithin_of_isWithin
set_option autoImplicit false

namespace LT
p2m_export "LT" "LatticeTree.Vertex.IsWithin LatticeTree.Vertex LatticeTree.unitOfNeZero"
namespace LatticeTree
p2m_export "LT.LatticeTree" "LatticeWithin Vertex.IsWithin latticeWithin_latticeMap_iff latticeMap latticeMap_mul latticeMap_mono scalarGL scalarGL_mul Homothetic Homothetic.symm Vertex Vertex.mk_eq_mk_iff unitOfNeZero"
p2m_open "LT.LatticeTree LT"

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

private theorem isWithin_add {c : Kˣ} {m n : ℕ} {a b d : Vertex R K} (h₁ : Vertex.IsWithin c m a b)
    (h₂ : Vertex.IsWithin c n b d) : Vertex.IsWithin c (m + n) a d := by
  obtain ⟨L, M, hL, hM, rfl, rfl, hLM⟩ := h₁
  obtain ⟨M₂, N, hM₂, hN, hb, rfl, hMN⟩ := h₂
  obtain ⟨u, rfl⟩ : Homothetic M₂ M := Vertex.mk_eq_mk_iff.mp hb
  have hMN' : LatticeWithin c n (latticeMap (scalarGL u) M₂) (latticeMap (scalarGL u) N) :=
    (latticeWithin_latticeMap_iff c n (scalarGL u) M₂ N).mpr hMN
  refine ⟨L, latticeMap (scalarGL u) N, hL, hN.map _, rfl, Vertex.mk_eq_mk_iff.mpr (Homothetic.symm ⟨u, rfl⟩),
    ?_, hMN'.2.trans hLM.2⟩
  rw [add_comm, pow_add, scalarGL_mul, latticeMap_mul]
  exact (latticeMap_mono _ hLM.1).trans hMN'.1

end LT.LatticeTree

theorem solution
    (R K : Type) [CommRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (v w x : LT.LatticeTree.Vertex R K) (n m : ℕ)
    (h₁ : LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) n v w)
    (h₂ : LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) m w x) :
    LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (n + m) v x := by
  exact LT.LatticeTree.isWithin_add h₁ h₂

end S_LT_LatticeTree_Vertex_isWithin_add_of_isWithin_of_isWithin
end P2MW
export P2MW.S_LT_LatticeTree_Vertex_isWithin_add_of_isWithin_of_isWithin (solution)
