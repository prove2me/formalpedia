-- Prove2me | solution 1 for OAI.Barnette.Network.Duality.simple_dual_edge
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T04:42:38.987991+00:00
-- url     : https://prove2.me/submissions/a2c145e9-ee0d-4d5d-ae55-1c5b38a54c29

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/ThreeCuts.lean:L40-L83
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.Duality.simple_dual_edge. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Quotients
import Definitions.Def_OAI_Combinatorics_Hamiltonian_DiskRegions
import Definitions.Def_OAI_Combinatorics_Hamiltonian_StateDisk
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Circulation
import Definitions.Def_OAI_Combinatorics_Hamiltonian_TriangleSystem
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ColoredDual
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CycleReversal
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPhases
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPolynomials
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Forest
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Contraction
import Definitions.Def_OAI_Combinatorics_Hamiltonian_MinorDuality
import Definitions.Def_OAI_Combinatorics_Hamiltonian_BMatching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Matching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ForestMatching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ThreeCuts

-- ---- from OAI.Combinatorics.Hamiltonian.CutSpaces ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Cuts, simplicity, and connectivity of finite oriented networks. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

end
end Barnette.Network

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} (N : Network V E)

variable [Fintype V] [Fintype E]
omit [Fintype V] in
lemma boundary_basis (e : E) : N.boundary (basisVec e) = fun v => N.incidence v e := by
  ext v
  rw [boundary_apply, Finset.sum_eq_single e]
  · simp [basisVec, incidence]
  · intro k _ hke; simp [basisVec, hke]
  · simp

variable {F : Type*} [Fintype F] (D : Network F E)

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

end
end Barnette.Network

end OAI

-- ---- from OAI.Combinatorics.Hamiltonian.ThreeCuts ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Three-edge cuts, capped graphs, and preservation of graph properties. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

lemma gradient_small_support_edge (h : N.ThreeEdgeConnected) (f : V → ℝ) (s : Finset E) (hs : s.card ≤ 2)
    (hf : ∀ e, e ∉ s → N.gradient f e = 0) : N.gradient f = 0 := by
  ext e
  by_contra he
  have hne : f (N.head e) ≠ f (N.tail e) := by
    simpa only [gradient_apply, Pi.zero_apply, sub_eq_zero] using he
  let A := Finset.univ.filter fun v => f v = f (N.tail e)
  have hin : A.Nonempty := ⟨N.tail e, by simp [A]⟩
  have hout : ∃ w, w ∉ A := ⟨N.head e, by simp [A, hne]⟩
  have hsub : N.cut A ⊆ s := by
    intro k hk
    by_contra hks
    have hg : f (N.head k) = f (N.tail k) := sub_eq_zero.mp (hf k hks)
    rcases (N.mem_cut A k).mp hk with ⟨ht,hh⟩ | ⟨hh,ht⟩
    · apply hh; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      exact hg.trans ht
    · apply ht; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
      exact hg.symm.trans hh
  have h₁ := h A hin (by obtain ⟨w,hw⟩ := hout; exact ⟨w,Finset.mem_compl.mpr hw⟩)
  have h₂ := Finset.card_le_card hsub
  omega

variable {F : Type*} [Fintype F] (D : Network F E)

omit [Fintype F] in
theorem Duality.simple_dual_edge (h : N.Duality D)
    (h3 : N.ThreeEdgeConnected) : D.Simple := by
  have lift_zero (x : E → ℝ) (hx : D.boundary x = 0)
      (s : Finset E) (hs : s.card ≤ 2) (hxs : ∀ e, e ∉ s → x e = 0) : x = 0 := by
    have hx' : x ∈ N.gradient.range := by rw [← h.dual_cycles_eq_cuts]; exact hx
    obtain ⟨f,hf⟩ := hx'
    rw [← hf]
    exact N.gradient_small_support_edge h3 f s hs (by simpa only [hf] using hxs)
  refine ⟨?_, ?_⟩
  · intro e he
    have hz : D.boundary (basisVec e) = 0 := by
      rw [D.boundary_basis]
      ext v
      simp [incidence, he]
    have hzero := lift_zero (basisVec e) hz {e} (by simp) (by
      intro k hk; simp only [Finset.mem_singleton] at hk; simp [basisVec, hk])
    have hh := congrFun hzero e
    norm_num [basisVec] at hh
  · intro e f hef
    by_contra hne
    rcases Sym2.eq_iff.mp hef with ⟨ht,hh⟩ | ⟨ht,hh⟩
    · have hz : D.boundary (basisVec e - basisVec f) = 0 := by
        rw [map_sub, D.boundary_basis, D.boundary_basis]
        ext v
        simp [incidence, ht, hh]
      have hzero := lift_zero (basisVec e - basisVec f) hz {e,f}
        (by simpa using Finset.card_insert_le e ({f} : Finset E))
        (by intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
            simp [basisVec, hk.1, hk.2])
      have hv := congrFun hzero e
      norm_num [basisVec, hne] at hv
    · have hz : D.boundary (basisVec e + basisVec f) = 0 := by
        rw [map_add, D.boundary_basis, D.boundary_basis]
        ext v
        dsimp [incidence]
        rw [ht, hh]
        ring
      have hzero := lift_zero (basisVec e + basisVec f) hz {e,f}
        (by simpa using Finset.card_insert_le e ({f} : Finset E))
        (by intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
            simp [basisVec, hk.1, hk.2])
      have hv := congrFun hzero e
      norm_num [basisVec, hne] at hv

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

variable {F : Type*} [Fintype F] (D : Network F E)

end
end Barnette.Network

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.Network.Duality.simple_dual_edge := @_root_.OAI.Barnette.Network.Duality.simple_dual_edge
