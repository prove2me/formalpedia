-- Prove2me | solution 1 for OAI.Barnette.Network.black_dual_card
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T04:24:32.723712+00:00
-- url     : https://prove2.me/submissions/6913b4eb-993d-4787-b463-2e3b51543633

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/MinorDuality.lean:L179-L192
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.black_dual_card. The node keeps its source
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
import Theorems.Thm_OAI_Barnette_Network_black_edge_partition
import Theorems.Thm_OAI_Barnette_Network_card_star
import Theorems.Thm_OAI_Barnette_Network_cubic_region_count

-- ---- from OAI.Combinatorics.Hamiltonian.Network ----
namespace OAI

/-! Oriented finite networks, cycle and cut spaces, and graph realization. -/

namespace Barnette

namespace Network
noncomputable section
variable {V E : Type*} (N : Network V E)

theorem gradient_eq_zero_iff (f : V → ℝ) :
    N.gradient f = 0 ↔ ∀ e, f (N.head e) = f (N.tail e) := by
  simp only [funext_iff, gradient_apply, Pi.zero_apply, sub_eq_zero]

theorem gradient_zero_adj {f : V → ℝ} (hf : N.gradient f = 0)
    {v w : V} (h : N.graph.Adj v w) : f v = f w := by
  obtain ⟨_, e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h
  · exact ((N.gradient_eq_zero_iff f).mp hf e).symm
  · exact (N.gradient_eq_zero_iff f).mp hf e

theorem gradient_zero_reachable {f : V → ℝ} (hf : N.gradient f = 0)
    {v w : V} (h : N.graph.Reachable v w) : f v = f w := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons h p ih => exact (N.gradient_zero_adj hf h).trans ih

theorem ker_gradient (h : N.graph.Connected) :
    N.gradient.ker = (constant (V := V)).range := by
  obtain ⟨v⟩ := h.nonempty
  ext f
  constructor
  · intro hf
    refine ⟨f v, ?_⟩
    ext w
    exact N.gradient_zero_reachable hf (h v w)
  · rintro ⟨a, rfl⟩
    exact N.gradient_const a

variable [Fintype V] [Fintype E]
attribute [local instance] OAI.Barnette.Network.instDecidableEq
attribute [local instance] OAI.Barnette.Network.instDecidableEq_1
omit [Fintype E] in
theorem gradient_matrix : N.gradient = Matrix.toLin' N.incidence.transpose := by
  classical
  apply LinearMap.ext
  intro f
  ext e
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, incidence,
    sub_mul, ite_mul, Finset.sum_sub_distrib]

omit [Fintype E] in
theorem rank_gradient (h : N.graph.Connected) :
    Module.finrank ℝ N.gradient.range + 1 = Fintype.card V := by
  obtain ⟨v⟩ := h.nonempty
  have hi : Function.Injective (constant (V := V)) := by
    intro a b hab
    exact congrFun hab v
  have hk : Module.finrank ℝ N.gradient.ker = 1 := by
    rw [N.ker_gradient h, LinearMap.finrank_range_of_inj hi]
    exact Module.finrank_self ℝ
  have hh := N.gradient.finrank_range_add_finrank_ker
  simpa only [hk, Module.finrank_pi] using hh

theorem rank_boundary (h : N.graph.Connected) :
    Module.finrank ℝ N.boundary.range + 1 = Fintype.card V := by
  have hh := N.rank_gradient h
  have he : Module.finrank ℝ N.boundary.range = Module.finrank ℝ N.gradient.range := by
    rw [N.gradient_matrix, boundary, Matrix.toLin'_apply', Matrix.toLin'_apply',
      ← Matrix.rank, ← Matrix.rank, Matrix.rank_transpose]
  rwa [he]

theorem dim_cycles (h : N.graph.Connected) :
    Module.finrank ℝ N.boundary.ker + Fintype.card V = Fintype.card E + 1 := by
  have hr := N.rank_boundary h
  have hk := N.boundary.finrank_range_add_finrank_ker
  rw [Module.finrank_pi] at hk
  omega

variable {F : Type*} [Fintype F] (D : Network F E)

theorem Duality.euler (h : N.Duality D) :
    Fintype.card V + Fintype.card F = Fintype.card E + 2 := by
  have h₁ := N.dim_cycles h.connected
  rw [h.cycles_eq_cuts] at h₁
  have h₂ := D.rank_gradient h.dual_connected
  omega

end
end Network
end Barnette

namespace Barnette
noncomputable section
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
  [DecidableRel G.Adj]

end
end Barnette

end OAI

-- ---- from OAI.Combinatorics.Hamiltonian.MinorDuality ----
namespace OAI

/-! Exact duality under finite network minors. -/

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
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

lemma black_dual_card (h : N.Duality D) (hN : N.Simple) (h3 : N.graph.IsRegularOfDegree 3)
    (black : V → Prop) (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) :
    Fintype.card F = (Finset.univ.filter black).card + 2 := by
  have hdeg : ∀ v, N.graph.degree v = 3 := h3
  have he := N.black_edge_partition black hc Finset.univ
  simp only [Finset.filter_true_of_mem (fun _ _ => Finset.mem_univ _),N.card_star hN,hdeg,
    Finset.sum_const,smul_eq_mul,Finset.card_univ] at he
  have hv := N.cubic_region_count hN h3 Finset.univ
  have hcut : N.cut Finset.univ = ∅ := by ext e; simp [cut]
  have hreg : N.regionEdges Finset.univ = Finset.univ := by ext e; simp [regionEdges]
  rw [hcut,hreg,Finset.card_empty,Finset.card_univ] at hv
  simp only [Finset.card_univ,add_zero] at hv
  have heu := h.euler N D
  omega

end
end Barnette.Network

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.Network.black_dual_card := @_root_.OAI.Barnette.Network.black_dual_card
