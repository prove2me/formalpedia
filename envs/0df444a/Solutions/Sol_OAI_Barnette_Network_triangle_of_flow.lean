-- Prove2me | solution 1 for OAI.Barnette.Network.triangle_of_flow
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:22:40.988687+00:00
-- url     : https://prove2.me/submissions/4a838a12-a736-4a7d-aaf1-83cdc05b271b

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/CutSpaces.lean:L234-L314
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.triangle_of_flow. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Theorems.Thm_OAI_Barnette_Network_flow_no_leaf

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
variable {F : Type*} [Fintype F] (D : Network F E)

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

omit [Fintype V] [Fintype E] in
lemma incident_iff_mem_pair (e : E) (v : V) :
    N.Incident e v ↔ v ∈ s(N.tail e, N.head e) := by
  simp only [Incident, Sym2.mem_iff]
  tauto

omit [Fintype V] [Fintype E] in
lemma pair_eq_of_incident {e : E} {v w : V} (hne : v ≠ w)
    (hv : N.Incident e v) (hw : N.Incident e w) : s(N.tail e,N.head e) = s(v,w) := by
  rcases hv with ht | hh <;> rcases hw with ht' | hh'
  · exact (hne (ht.symm.trans ht')).elim
  · rw [ht,hh']
  · rw [ht',hh,Sym2.eq_swap]
  · exact (hne (hh.symm.trans hh')).elim

omit [Fintype V] [Fintype E] in
lemma Simple.incident_other (h : N.Simple) {e : E} {v : V} (hi : N.Incident e v) :
    ∃ w, v ≠ w ∧ s(N.tail e,N.head e) = s(v,w) := by
  rcases hi with ht | hh
  · exact ⟨N.head e, ht ▸ h.loopless e, by rw [ht]⟩
  · exact ⟨N.tail e, hh ▸ (h.loopless e).symm, by rw [hh,Sym2.eq_swap]⟩

omit [Fintype V] in

theorem triangle_of_flow (hN : N.Simple) (x : E → ℝ) (hx : N.boundary x = 0)
    (hs : (N.flowSupport x).card = 3) : Nonempty (N.Triangle (N.flowSupport x)) := by
  let s := N.flowSupport x
  have hspos : s.Nonempty := Finset.card_pos.mp (by dsimp [s]; omega)
  obtain ⟨e,he⟩ := hspos
  have hxe : x e ≠ 0 := (N.mem_flowSupport x e).mp he
  let a := N.tail e
  let b := N.head e
  have hab : a ≠ b := hN.loopless e
  obtain ⟨f,hfe,hxf,hfa⟩ := N.flow_no_leaf hN x hx hxe (Or.inl rfl)
  have hf : f ∈ s := (N.mem_flowSupport x f).mpr hxf
  obtain ⟨c,hac,hfc⟩ := hN.incident_other N hfa
  have hbc : b ≠ c := by
    intro hbc
    have hef : e = f := hN.pair_injective (by dsimp [a,b] at hfc ⊢; rw [hfc, ← hbc])
    exact hfe hef.symm
  have hferase : f ∈ s.erase e := Finset.mem_erase.mpr ⟨hfe,hf⟩
  have hrest : ((s.erase e).erase f).card = 1 := by
    rw [Finset.card_erase_of_mem hferase, Finset.card_erase_of_mem he]
    dsimp [s]; omega
  obtain ⟨g,hg⟩ := Finset.card_eq_one.mp hrest
  have hsEq : s = {e,f,g} := by
    calc s = insert e (s.erase e) := (Finset.insert_erase he).symm
         _ = insert e (insert f ((s.erase e).erase f)) := by rw [Finset.insert_erase hferase]
         _ = _ := by rw [hg]
  have hgmem : g ∈ (s.erase e).erase f := by rw [hg]; simp
  obtain ⟨hgf,hge,hgs⟩ := by
    simpa only [Finset.mem_erase, and_assoc] using hgmem
  have fnotb : ¬N.Incident f b := by
    rw [N.incident_iff_mem_pair, hfc]
    simp only [Sym2.mem_iff]
    exact fun h => h.elim (fun h => hab h.symm) hbc
  have enotc : ¬N.Incident e c := by
    rw [N.incident_iff_mem_pair]
    show ¬(c ∈ s(a,b))
    simp only [Sym2.mem_iff]
    exact fun h => h.elim (fun h => hac h.symm) (fun h => hbc h.symm)
  have hgb : N.Incident g b := by
    obtain ⟨k,hke,hxk,hkb⟩ := N.flow_no_leaf hN x hx hxe (Or.inr rfl)
    have hk : k ∈ s := (N.mem_flowSupport x k).mpr hxk
    rw [hsEq] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · exact (hke rfl).elim
    · exact (fnotb hkb).elim
    · exact hkb
  have hgc : N.Incident g c := by
    have hfc' : N.Incident f c := (N.incident_iff_mem_pair f c).mpr (by rw [hfc]; simp)
    obtain ⟨k,hkf,hxk,hkc⟩ := N.flow_no_leaf hN x hx hxf hfc'
    have hk : k ∈ s := (N.mem_flowSupport x k).mpr hxk
    rw [hsEq] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · exact (enotc hkc).elim
    · exact (hkf rfl).elim
    · exact hkc
  have hgend := N.pair_eq_of_incident hbc hgb hgc
  refine ⟨{
    corner := ![a,b,c]
    corner_injective := ?_
    edge := ![e,g,f]
    edge_injective := ?_
    edge_range := ?_
    edge_ends := ?_ }⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> dsimp at hij <;> first | rfl | exact (hab hij).elim | exact (hab hij.symm).elim | exact (hac hij).elim | exact (hac hij.symm).elim | exact (hbc hij).elim | exact (hbc hij.symm).elim
  · intro i j hij
    fin_cases i <;> fin_cases j <;> dsimp at hij <;> first | rfl | exact (hge hij).elim | exact (hge hij.symm).elim | exact (hfe hij).elim | exact (hfe hij.symm).elim | exact (hgf hij).elim | exact (hgf hij.symm).elim
  · change Finset.univ.image ![e,g,f] = s
    rw [hsEq]
    ext k
    simp [Fin.exists_fin_succ]
    tauto
  · intro i
    fin_cases i
    · rfl
    · exact hgend
    · change s(N.tail f, N.head f) = s(c,a)
      exact hfc.trans Sym2.eq_swap

end
end Barnette.Network

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.Network.triangle_of_flow := @_root_.OAI.Barnette.Network.triangle_of_flow
