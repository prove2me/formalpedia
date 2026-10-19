-- Prove2me | solution 1 for OAI.Barnette.Network.whiteCharge_cut_integral
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:52:31.208783+00:00
-- url     : https://prove2.me/submissions/4376367b-2159-4c8b-9280-6bc0fe74b5d5

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/Circulation.lean:L208-L224
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.whiteCharge_cut_integral. The node keeps its source
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

-- ---- from OAI.Combinatorics.Hamiltonian.Network ----
namespace OAI

/-! Oriented finite networks, cycle and cut spaces, and graph realization. -/

namespace Barnette

namespace Network
noncomputable section
variable {V E : Type*} (N : Network V E)

variable [Fintype V] [Fintype E]
attribute [local instance] OAI.Barnette.Network.instDecidableEq
attribute [local instance] OAI.Barnette.Network.instDecidableEq_1
theorem boundary_adjoint (x : E → ℝ) (f : V → ℝ) :
    ∑ v, N.boundary x v * f v = ∑ e, x e * N.gradient f e := by
  classical
  simp only [boundary_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp [sub_mul, ite_mul, Finset.sum_sub_distrib, mul_sub]

variable {F : Type*} [Fintype F] (D : Network F E)

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

-- ---- from OAI.Combinatorics.Hamiltonian.Circulation ----
namespace OAI

/-! Oriented triangular faces and positive white-face charges. -/

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

lemma whiteCharge_inside (black : V → Prop) (root : V) (A : Finset V)
    (hr : root ∉ A) :
    ∑ v ∈ A, whiteCharge black root v = ((A.filter fun v => ¬black v).card : ℝ) := by
  trans ∑ v ∈ A, if ¬black v then (1:ℝ) else 0
  · apply Finset.sum_congr rfl
    intro v hv
    have hvr : v ≠ root := fun hh => hr (hh ▸ hv)
    by_cases hb : black v <;> simp [whiteCharge,hb,hvr]
  · exact Finset.sum_boole _ _

lemma whiteCharge_cut_integral (black : V → Prop) (root : V) (A : Finset V)
    (hr : root ∉ A) (α : E → ℝ) (hα : N.boundary α = whiteCharge black root)
    (c : ℝ) (x : E → ℝ)
    (hx : x = c • N.gradient (fun v => if v ∈ A then 1 else 0)) :
    ∑ e, α e * x e = c * ((A.filter fun v => ¬black v).card : ℝ) := by
  simp only [hx,Pi.smul_apply,smul_eq_mul]
  have hh : ∑ e, α e * (c * N.gradient (fun v => if v ∈ A then 1 else 0) e) =
      c * ∑ e, α e * N.gradient (fun v => if v ∈ A then 1 else 0) e := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [hh,← N.boundary_adjoint,hα]
  congr 1
  simp only [mul_ite,mul_one,mul_zero]
  rw [← Finset.sum_filter]
  simpa only [Finset.filter_mem_eq_inter,Finset.univ_inter] using whiteCharge_inside black root A hr

end
end Barnette.Network

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.Network.whiteCharge_cut_integral := @_root_.OAI.Barnette.Network.whiteCharge_cut_integral
