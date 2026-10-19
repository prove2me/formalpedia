-- Prove2me | solution 1 for OAI.Barnette.Network.ColoredDual.remainder_black_degree
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T04:36:51.394858+00:00
-- url     : https://prove2.me/submissions/033b4e07-42a4-477d-b1a9-52731e4da9cc

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/Matching.lean:L448-L480
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.ColoredDual.remainder_black_degree. The node keeps its source
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
import Theorems.Thm_OAI_Barnette_Network_ColoredDual_removed_at_black
import Theorems.Thm_OAI_Barnette_Network_card_star

-- ---- from OAI.Combinatorics.Hamiltonian.Matching ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

/-! Disk and spoke signs and matching complements. -/

namespace Barnette.CycleCoordinates
variable {V : Type*} {G : SimpleGraph V} (C : Barnette.CycleCoordinates G)
end Barnette.CycleCoordinates

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

variable {F : Type*} [Fintype F] (D : Network F E)
end
end Barnette.Network

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V A : Type*} (Q : Network V A)

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

end
end Barnette.Network
namespace Barnette.Network.ColoredDual
noncomputable section
open scoped Classical
open Barnette.TriangleSystem
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D) {root : V}

end
end Barnette.Network.ColoredDual
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} (D : Network V E)

end
end Barnette.Network

namespace Barnette.Network.ColoredDual
noncomputable section
open scoped Classical
open Barnette.TriangleSystem
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D) {root : V}

omit [Fintype F] in
lemma remainder_black_degree (P : (M.system root).Pair (M.nonroots root)) (hr : M.black root)
    (i : Fin 3) (v : V) (hv : M.black v) :
    ((N.star v).filter fun e => e ∈ (M.removed P i)ᶜ).card = if v = root then 1 else 2 := by
  by_cases hh : v = root
  · subst v
    rw [ite_eq_left rfl]
    have he : (N.star root).filter (fun e => e ∈ (M.removed P i)ᶜ) = {(M.face root).edge i} := by
      ext e
      simp only [Finset.mem_filter,Finset.mem_compl,Finset.mem_singleton]
      constructor
      · rintro ⟨he,hn⟩
        have hm := M.removed_at_black P hr i root hr he
        simpa using (not_congr hm).mp hn
      · intro heq; subst e
        have hm : (M.face root).edge i ∈ N.star root := by
          have hx : (M.face root).edge i ∈ Finset.univ.image (M.face root).edge := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
          simpa only [(M.face root).edge_range] using hx
        exact ⟨hm,by rw [M.removed_at_black P hr i root hr hm]; simp⟩
    rw [he,Finset.card_singleton]
  · rw [ite_eq_right hh]
    have he : (N.star v).filter (fun e => e ∈ (M.removed P i)ᶜ) =
        (N.star v).erase (M.qLabel P ⟨v,hv,hh⟩) := by
      ext e
      simp only [Finset.mem_filter,Finset.mem_compl,Finset.mem_erase]
      constructor
      · rintro ⟨he,hn⟩
        have hm := M.removed_at_black P hr i v hv he
        simp only [dite_eq_right hh] at hm
        exact ⟨(not_congr hm).mp hn,he⟩
      · rintro ⟨hn,he⟩
        exact ⟨he,by rw [M.removed_at_black P hr i v hv he]; simpa [hh]⟩
    rw [he,Finset.card_erase_of_mem (show M.qLabel P ⟨v,hv,hh⟩ ∈ N.star v from (M.face v).side_mem D _ _),N.card_star M.simple,M.cubic v]

end
end Barnette.Network.ColoredDual

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.Network OAI.Barnette.Network.ColoredDual
open scoped Classical
open Barnette.TriangleSystem


theorem solution : type_of% @_root_.OAI.Barnette.Network.ColoredDual.remainder_black_degree := @_root_.OAI.Barnette.Network.ColoredDual.remainder_black_degree
