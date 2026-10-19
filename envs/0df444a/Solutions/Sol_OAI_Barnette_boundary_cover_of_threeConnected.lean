-- Prove2me | solution 1 for OAI.Barnette.boundary_cover_of_threeConnected
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:19:18.176685+00:00
-- url     : https://prove2.me/submissions/31f12fbb-5d23-4252-b1bb-8b332d3ce715

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/Network.lean:L239-L261
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.boundary_cover_of_threeConnected. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network

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
variable {F : Type*} [Fintype F] (D : Network F E)

end
end Network
end Barnette

namespace Barnette
noncomputable section
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
  [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in

lemma boundary_cover_of_threeConnected (h : ThreeVertexConnected G)
    (A S : Finset V) (hS : S.card ≤ 2) (hSA : S ⊆ A)
    (hout : ∃ w, w ∉ A)
    (hboundary : ∀ v ∈ A, ∀ w, w ∉ A → G.Adj v w → v ∈ S) : A ⊆ S := by
  intro v hv
  by_contra hvS
  obtain ⟨w, hw⟩ := hout
  have hwS : w ∉ S := fun hs => hw (hSA hs)
  let H := G.induce {v | v ∉ S}
  have hr := (h.2 S hS) (⟨v,hvS⟩ : {v | v ∉ S}) ⟨w,hwS⟩
  obtain ⟨p⟩ := hr
  have hp : ∀ {a b : {v | v ∉ S}}, H.Walk a b → a.val ∈ A → b.val ∈ A := by
    intro a b p
    induction p with
    | nil => exact id
    | @cons a z b haz p ih =>
      intro ha
      apply ih
      by_contra hz
      exact a.property (hboundary a.val ha z.val hz haz)
  exact hw (hp p hv)

end
end Barnette

end OAI

-- ---- platform node ----
open OAI OAI.Barnette
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.boundary_cover_of_threeConnected := @_root_.OAI.Barnette.boundary_cover_of_threeConnected
