-- Prove2me | solution 1 for OAI.Barnette.Network.tree_matching
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T04:38:27.270437+00:00
-- url     : https://prove2.me/submissions/191faf30-544d-4f02-9a3c-b3f6278a658b

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/ForestMatching.lean:L55-L152
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.tree_matching. The node keeps its source
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
import Theorems.Thm_OAI_Barnette_Network_black_edge_partition
import Theorems.Thm_OAI_Barnette_Network_independent_edges_bound

-- ---- from OAI.Combinatorics.Hamiltonian.StateDisk ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-! Minimal links, incidence states, and the signed disk identity. -/

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

omit [Fintype V] [Fintype E] [Fintype F] in
lemma blackEndpoint_spec (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) (e : E) :
    black (N.blackEndpoint black e) ∧ N.Incident e (N.blackEndpoint black e) := by
  by_cases ht : black (N.tail e)
  · simp only [blackEndpoint,ite_eq_left ht]; exact ⟨ht,Or.inl rfl⟩
  · simp only [blackEndpoint,ite_eq_right ht]
    exact ⟨not_not.mp (fun hh => ht ((hc e).mpr hh)),Or.inr rfl⟩

end
end Barnette.Network

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

end
end Barnette.Network

end OAI

-- ---- from OAI.Combinatorics.Hamiltonian.ForestMatching ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! From opposite forests to connected spanning matching complements. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

omit [Fintype V] [Fintype E] in
lemma complement_coloring (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) :
    ∀ e, ¬black (N.tail e) ↔ ¬¬black (N.head e) := fun e => not_congr (hc e)

omit [Fintype V] [Fintype E] in
lemma colored_endpoints (black : V → Prop)
    (_hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) (e : E) :
    s(N.tail e,N.head e) = s(N.blackEndpoint black e,N.blackEndpoint (fun v => ¬black v) e) := by
  by_cases hb : black (N.tail e)
  · simp [blackEndpoint,hb]
  · simp [blackEndpoint,hb,Sym2.eq_swap]

lemma black_fiber_count (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (H : Finset E) (T : Finset V) (hT : ∀ v ∈ T, black v) :
    (H.filter fun e => N.blackEndpoint black e ∈ T).card =
      ∑ v ∈ T, ((N.star v).filter fun e => e ∈ H).card := by
  rw [← N.black_edge_partition black hc]
  have hf (v : V) (hv : black v) :
      (N.star v).filter (fun e => e ∈ H.filter (fun e => N.blackEndpoint black e ∈ T)) =
        if v ∈ T then (N.star v).filter (fun e => e ∈ H) else ∅ := by
    ext e
    by_cases ht : v ∈ T
    · simp only [ite_eq_left ht,Finset.mem_filter]
      constructor
      · tauto
      · rintro ⟨he,hh⟩
        exact ⟨he,hh,(N.blackEndpoint_eq black hc hv ((N.mem_star _ _).mp he)) ▸ ht⟩
    · simp only [ite_eq_right ht,Finset.notMem_empty,Finset.mem_filter,iff_false]
      rintro ⟨he,_,hbe⟩
      exact ht ((N.blackEndpoint_eq black hc hv ((N.mem_star _ _).mp he)) ▸ hbe)
  rw [Finset.sum_congr rfl (fun v hv => congrArg Finset.card (hf v (Finset.mem_filter.mp hv).2))]
  simp only [apply_ite Finset.card,Finset.card_empty,Finset.sum_ite_mem]
  apply Finset.sum_congr ?_ (fun _ _ => rfl)
  ext v
  simp only [Finset.mem_inter,Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨And.right,fun hv => ⟨hT v hv,hv⟩⟩

lemma tree_matching (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (H : Finset E) (hi : Function.Injective (N.restrict (Subtype.val : H → E)).boundary)
    (root : V) (_hr : black root)
    (hd : ∀ v, black v → ((N.star v).filter (fun e => e ∈ H)).card = if v = root then 1 else 2)
    (hbal : Fintype.card {v // black v} = Fintype.card {v // ¬black v}) :
    ∃ P : Finset E, P ⊆ H ∧ ∀ v, ((N.star v).filter fun e => e ∈ P).card = 1 := by
  let B := {v // black v}
  let W := {v // ¬black v}
  let R : B → W → Prop := fun b w => ∃ e ∈ H,
    N.blackEndpoint black e = b.val ∧ N.blackEndpoint (fun v => ¬black v) e = w.val
  have hhall (S : Finset B) : S.card ≤ (Finset.univ.filter fun w : W => ∃ b ∈ S, R b w).card := by
    let Y := Finset.univ.filter fun w : W => ∃ b ∈ S, R b w
    let T := S.image Subtype.val
    let Z := Y.image Subtype.val
    let J := H.filter fun e => N.blackEndpoint black e ∈ T
    have hTc : T.card = S.card := Finset.card_image_of_injective _ Subtype.val_injective
    have hZc : Z.card = Y.card := Finset.card_image_of_injective _ Subtype.val_injective
    have hT : ∀ v ∈ T, black v := by
      intro v hv; obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hv; exact b.property
    have hZ : ∀ v ∈ Z, ¬black v := by
      intro v hv; obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hv; exact w.property
    have hdis : Disjoint T Z := Finset.disjoint_left.mpr (fun v ht hz => hZ v hz (hT v ht))
    by_cases hS : S.Nonempty
    · have hJc : 2*T.card ≤ J.card + 1 := by
        have he := N.black_fiber_count black hc H T hT
        have hd' : ∀ v ∈ T, ((N.star v).filter fun e => e ∈ H).card = 2 - if v = root then 1 else 0 := by
          intro v hv; rw [hd v (hT v hv)]; split_ifs <;> rfl
        have hn (v : V) : (2 - if v = root then 1 else 0 : ℕ) + (if v = root then 1 else 0) = 2 := by split_ifs <;> rfl
        have hh : J.card + ∑ v ∈ T, (if v = root then 1 else 0 : ℕ) = 2*T.card := by
          rw [he,Finset.sum_congr rfl hd',← Finset.sum_add_distrib]
          simp only [hn,Finset.sum_const,smul_eq_mul,mul_comm]
        have hx : (∑ v ∈ T, (if v = root then 1 else 0 : ℕ)) ≤ 1 := by simp; split_ifs <;> omega
        omega
      let J' : Finset H := Finset.univ.filter fun e => e.val ∈ J
      have hJ' : J'.card = J.card := by
        apply Finset.card_bij (fun e _ => e.val)
        · intro e he; exact (Finset.mem_filter.mp he).2
        · intro _ _ _ _ hh; exact Subtype.ext hh
        · intro e he; exact ⟨⟨e,(Finset.mem_filter.mp he).1⟩,by simp [J',he],rfl⟩
      have hn : (T ∪ Z).Nonempty := by obtain ⟨b,hb⟩ := hS; exact ⟨b.val,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨b,hb,rfl⟩)⟩
      have hsupp : ∀ e ∈ J', (N.restrict (Subtype.val : H → E)).tail e ∈ T ∪ Z ∧
          (N.restrict (Subtype.val : H → E)).head e ∈ T ∪ Z := by
        intro e he
        have hJ : e.val ∈ J := (Finset.mem_filter.mp he).2
        have hb : N.blackEndpoint black e.val ∈ T := (Finset.mem_filter.mp hJ).2
        obtain ⟨b,hbS,hbe⟩ := Finset.mem_image.mp hb
        let w : W := ⟨N.blackEndpoint (fun v => ¬black v) e.val,
          (N.blackEndpoint_spec (fun v => ¬black v) (N.complement_coloring black hc) e.val).1⟩
        have hw : w ∈ Y := by
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,b,hbS,e.val,e.property,hbe.symm,rfl⟩
        have hz : N.blackEndpoint (fun v => ¬black v) e.val ∈ Z := Finset.mem_image.mpr ⟨w,hw,rfl⟩
        rcases Sym2.eq_iff.mp (N.colored_endpoints black hc e.val) with hh|hh
        · exact ⟨Finset.mem_union_left _ (hh.1 ▸ hb),Finset.mem_union_right _ (hh.2 ▸ hz)⟩
        · exact ⟨Finset.mem_union_right _ (hh.1 ▸ hz),Finset.mem_union_left _ (hh.2 ▸ hb)⟩
      have hb := (N.restrict (Subtype.val : H → E)).independent_edges_bound hi J' (T ∪ Z) hn hsupp
      rw [hJ',Finset.card_union_of_disjoint hdis,hTc,hZc] at hb
      rw [hTc] at hJc
      change S.card ≤ Y.card
      omega
    · have hz : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      simp [hz]
  obtain ⟨f,hfi,hf⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective R).mp hhall
  have hfs : Function.Surjective f := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfi,hbal⟩ |>.2
  choose p hp hb hw using hf
  let P := Finset.univ.image p
  have hpP (b : B) : p b ∈ P := Finset.mem_image.mpr ⟨b,Finset.mem_univ _,rfl⟩
  have hsub : P ⊆ H := by intro e he; obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp he; exact hp b
  refine ⟨P,hsub,?_⟩
  intro v
  by_cases hv : black v
  · let b : B := ⟨v,hv⟩
    apply Finset.card_eq_one.mpr
    refine ⟨p b,?_⟩
    ext e
    simp only [Finset.mem_filter,Finset.mem_singleton]
    constructor
    · rintro ⟨he,hP⟩
      obtain ⟨b',_,rfl⟩ := Finset.mem_image.mp hP
      have hh : b' = b := Subtype.ext ((hb b').symm.trans (N.blackEndpoint_eq black hc hv ((N.mem_star _ _).mp he)))
      rw [hh]
    · rintro rfl
      have hh : N.blackEndpoint black (p b) = v := hb b
      exact ⟨(N.mem_star _ _).mpr (hh ▸ (N.blackEndpoint_spec black hc (p b)).2),hpP b⟩
  · obtain ⟨b,hbv⟩ := hfs ⟨v,hv⟩
    have hwv : N.blackEndpoint (fun v => ¬black v) (p b) = v := (hw b).trans (congrArg Subtype.val hbv)
    apply Finset.card_eq_one.mpr
    refine ⟨p b,?_⟩
    ext e
    simp only [Finset.mem_filter,Finset.mem_singleton]
    constructor
    · rintro ⟨he,hP⟩
      obtain ⟨b',_,rfl⟩ := Finset.mem_image.mp hP
      have hh : f b' = f b := Subtype.ext ((hw b').symm.trans
        ((N.blackEndpoint_eq (fun v => ¬black v) (N.complement_coloring black hc) hv ((N.mem_star _ _).mp he)).trans ((congrArg Subtype.val hbv).symm)))
      rw [hfi hh]
    · rintro rfl
      exact ⟨(N.mem_star _ _).mpr (hwv ▸ (N.blackEndpoint_spec (fun v => ¬black v) (N.complement_coloring black hc) (p b)).2),hpP b⟩
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
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D) {root : V}

end
end Barnette.Network.ColoredDual
namespace Barnette.CycleCoordinates
variable {V : Type*} {G : SimpleGraph V} (C : Barnette.CycleCoordinates G)
end Barnette.CycleCoordinates

namespace Barnette.Network
noncomputable section
variable {V E : Type*} (N : Network V E)
end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype E] (N : Network V E)

end
end Barnette.Network

namespace Barnette.Network.ColoredDual
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D) {root : V}

end
end Barnette.Network.ColoredDual

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.Network.tree_matching := @_root_.OAI.Barnette.Network.tree_matching
