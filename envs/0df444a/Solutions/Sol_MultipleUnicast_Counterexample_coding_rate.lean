-- Prove2me | solution 1 for MultipleUnicast.Counterexample.coding_rate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T10:27:05.258229+00:00
-- url     : https://prove2.me/submissions/facb0e2b-5509-4c95-bcbc-c879ed882bf5

import Mathlib
import Definitions.Def_MultipleUnicast_Counterexample_Graph
import Definitions.Def_MultipleUnicast_Counterexample_Protocol
import Definitions.Def_MultipleUnicast_Counterexample_LocalSpace
import Theorems.Thm_MultipleUnicast_Counterexample_balanced_orientation
import Theorems.Thm_MultipleUnicast_Counterexample_restriction_isomorphism

section
set_option maxRecDepth 4096
set_option autoImplicit false
namespace MultipleUnicast.Counterexample.Dev.Bal
open MultipleUnicast.Counterexample


end MultipleUnicast.Counterexample.Dev.Bal
end

section
set_option maxRecDepth 4096
set_option autoImplicit false

namespace MultipleUnicast.Counterexample.Dev.TermDist
open MultipleUnicast.Counterexample MultipleUnicast.Counterexample.Dev.Bal Matrix

/-! ### Spanning-tree certificate: `parL v` is a physical edge joining `v` to `upL v`,
and `depL (upL v) < depL v`. -/

/-! ### Bipartiteness -/

/-! ### Every candidate edge is an incidence -/

/-! ### Two distinct points lie on at most one common line -/

/-! ### No short walks between the ends of a deleted edge -/

end MultipleUnicast.Counterexample.Dev.TermDist

namespace MultipleUnicast.Counterexample


end MultipleUnicast.Counterexample
end

section
set_option maxRecDepth 2048
set_option autoImplicit false
set_option Elab.async false

/-! Local part of `restriction_isomorphism`: the five known positions at a vertex determine
the five local coefficients, and local interpolation is a linear left inverse. -/

namespace MultipleUnicast.Counterexample.Dev.RILocal
open MultipleUnicast.Counterexample MultipleUnicast.Counterexample.Dev.TermDist Matrix

/-! ### Binary quartic forms -/

/-! ### Two-dimensional orthogonal complements -/

/-! ### Endpoints and the artificial orientation -/

/-! ### Neighbours of a vertex -/

/-! ### The basis `U, W` of the orthogonal complement -/

end MultipleUnicast.Counterexample.Dev.RILocal

namespace MultipleUnicast.Counterexample.Dev.RI
open MultipleUnicast.Counterexample MultipleUnicast.Counterexample.Dev.RILocal

end MultipleUnicast.Counterexample.Dev.RI
end

section
set_option maxRecDepth 2048
set_option autoImplicit false
set_option Elab.async false

namespace MultipleUnicast.Counterexample.Dev.RIGlobal
open MultipleUnicast.Counterexample

/-! ### The processing order -/

theorem perm : processingOrder.Perm (List.finRange 182) :=
  balanced_orientation.2.2.2.1

theorem mem_order (v : Vertex) : v ∈ processingOrder :=
  perm.mem_iff.2 (List.mem_finRange v)

theorem nodup_order : processingOrder.Nodup :=
  perm.nodup_iff.2 (List.nodup_finRange 182)

theorem position_inj {u v : Vertex} (h : position u = position v) : u = v :=
  (List.idxOf_inj (mem_order u)).1 h

/-! ### Orientation facts -/

theorem pe_ne_le (q : Edge) : pointEnd q ≠ lineEnd q := by
  intro h
  have h1 : (pointEnd q).val < 91 := (edgePair q).1.isLt
  have h2 : 91 ≤ (lineEnd q).val := Nat.le_add_right _ _
  rw [h] at h1; omega

theorem incident_tail (q : Edge) : incident (tail q) q := by
  unfold tail earlier later incident; split_ifs <;> simp

theorem incident_head (q : Edge) : incident (head q) q := by
  unfold head earlier later incident; split_ifs <;> simp

theorem pos_tail_lt (q : Edge) (hq : q ∉ deleted) : position (tail q) < position (head q) := by
  unfold tail head earlier later
  rw [if_neg hq, if_neg hq]
  split_ifs with h
  · exact h
  · have hne : position (pointEnd q) ≠ position (lineEnd q) := fun h' => pe_ne_le q (position_inj h')
    omega

theorem known_incident {v : Vertex} {p : Edge} (hp : p ∈ knownPositions v) : incident v p := by
  unfold knownPositions at hp
  rcases (Finset.mem_filter.1 hp).2 with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
  · exact h ▸ incident_head p
  · exact h ▸ incident_head p
  · exact h

/-! ### Local coefficients of elements of `W` -/

theorem WC_W (w : WC) : w.val ∈ W := (Submodule.mem_inf.1 w.prop).1

theorem WC_C (w : WC) (q : Edge) (hq : q ∈ C) : w.val q = 0 := by
  have h := (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 w.prop).2 ⟨q, hq⟩
  rw [LinearMap.mem_ker] at h
  exact h

theorem not_deleted_of_physical {p : Edge} (hp : p ∈ physical) : p ∉ deleted :=
  (Finset.mem_sdiff.1 hp).2

theorem not_physical_of_B {p : Edge} (hp : p ∈ B) : p ∉ physical := fun h =>
  not_deleted_of_physical h (Finset.mem_sdiff.1 hp).1

/-! ### Injectivity -/

/-! ### Dimension count -/

/-! ### The execution computes the preimage -/

end MultipleUnicast.Counterexample.Dev.RIGlobal

namespace MultipleUnicast.Counterexample
open Dev.RIGlobal

end MultipleUnicast.Counterexample
end

section
set_option maxRecDepth 2048
set_option autoImplicit false
set_option Elab.async false
open scoped Classical

namespace MultipleUnicast.Counterexample.Dev.CRCode
open MultipleUnicast.Counterexample

attribute [local irreducible] execution
open MultipleUnicast.Counterexample.Dev.RIGlobal

/-! ### Orientation facts -/

theorem tail_of_del {q : Edge} (h : q ∈ deleted) : tail q = later q := by unfold tail; rw [if_pos h]
theorem head_of_del {q : Edge} (h : q ∈ deleted) : head q = earlier q := by unfold head; rw [if_pos h]
theorem tail_of_nd {q : Edge} (h : q ∉ deleted) : tail q = earlier q := by unfold tail; rw [if_neg h]
theorem head_of_nd {q : Edge} (h : q ∉ deleted) : head q = later q := by unfold head; rw [if_neg h]

theorem del_of_B {q : Edge} (h : q ∈ B) : q ∈ deleted := (Finset.mem_sdiff.1 h).1

theorem earlier_ne_later (q : Edge) : earlier q ≠ later q := by
  unfold earlier later
  split_ifs
  · exact pe_ne_le q
  · exact (pe_ne_le q).symm

theorem adj_earlier_later {q : Edge} (hq : q ∈ physical) : graph.Adj (earlier q) (later q) := by
  show physicalAdj _ _
  refine ⟨q, hq, ?_⟩
  unfold earlier later
  split_ifs
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

theorem network_t (i : Fin network.k) : network.t i = later (sessionEquiv i).val := rfl
theorem network_C (u v : Vertex) : network.C u v = if graph.Adj u v then 1 else 0 := rfl

attribute [local irreducible] earlier later edgePair incidenceList processingOrder
  deleted physical C B

/-! ### Local uniqueness and determination -/

theorem LI : LocalInterpolation := restriction_isomorphism.2.1

theorem local_unique' (v : Vertex) (a b : Coefficients)
    (h : ∀ q ∈ knownPositions v, localEvaluation v a q = localEvaluation v b q) : a = b := by
  obtain ⟨hcard, L, hL1, -⟩ := LI v
  let E : Coefficients →ₗ[F9] ({q : Edge // q ∈ knownPositions v} → F9) :=
    (LinearMap.pi fun p => LinearMap.proj p.val).comp (localEvaluation v)
  have hE : ∀ c p, E c p = localEvaluation v c p.val := fun _ _ => rfl
  have hsurj : Function.Surjective E := fun y => ⟨L y, funext fun p => by rw [hE, hL1]⟩
  have hdim : Module.finrank F9 Coefficients =
      Module.finrank F9 ({q : Edge // q ∈ knownPositions v} → F9) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin, Fintype.card_coe, hcard]
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj
  exact hinj (funext fun p => by rw [hE, hE, h p.val p.prop])

theorem coeffs' {w : Edge → F9} (hw : w ∈ W) (v : Vertex) :
    ∃ a : Coefficients, ∀ q, incident v q → localEvaluation v a q = w q := by
  have h := (Submodule.mem_iInf _).1 hw v
  rw [Submodule.mem_comap, LinearMap.mem_range] at h
  obtain ⟨a, ha⟩ := h
  refine ⟨a, fun q hq => ?_⟩
  rw [ha]
  show (if incident v q then w q else 0) = w q
  rw [if_pos hq]

theorem det {w : Edge → F9} (hw : w ∈ W) (v : Vertex) (y : Edge → F9)
    (hy : ∀ p ∈ knownPositions v, y p = w p) :
    ∀ q, incident v q → localEvaluation v (interpolate v y) q = w q := by
  obtain ⟨a, ha⟩ := coeffs' hw v
  obtain ⟨-, L, hL1, hL2⟩ := LI v
  have hI : interpolate v y = a := by
    rw [hL2]
    apply local_unique'
    intro p hp
    rw [hL1 _ ⟨p, hp⟩, ha p (known_incident hp), hy p hp]
  intro q hq
  rw [hI, ha q hq]

/-! ### The execution is the inverse of restriction -/

noncomputable def eqv : WC ≃ₗ[F9] Input :=
  LinearEquiv.ofBijective restriction restriction_isomorphism.1

theorem exec_eq (x : Input) : execution x = (eqv.symm x).val := by
  obtain ⟨w, ⟨h1, h2⟩, -⟩ := restriction_isomorphism.2.2 x
  have : eqv.symm x = w := by
    rw [LinearEquiv.symm_apply_eq]; exact h1.symm
  rw [h2, this]

theorem restr_symm (x : Input) (q : Session) : (eqv.symm x).val q.val = x q :=
  congrFun (eqv.apply_symm_apply x) q

/-- The execution value on an edge is the local evaluation at its tail of the
interpolation of the data available there. -/
theorem exec_local (x : Input) (q : Edge) :
    execution x q =
      localEvaluation (tail q) (interpolate (tail q) (available (tail q) x (execution x))) q := by
  have hw := exec_eq x
  have h := det (WC_W (eqv.symm x)) (tail q) (available (tail q) x (execution x)) ?_ q
    (incident_tail q)
  · rw [h, hw]
  intro p hp
  unfold available
  rw [hw]
  by_cases hC : p ∈ C
  · rw [if_pos hC, WC_C _ p hC]
  rw [if_neg hC]
  by_cases hB : p ∈ B
  · rw [dif_pos hB]
    split_ifs
    · exact (restr_symm x ⟨p, hB⟩).symm
    · rfl
  · rw [dif_neg hB]

/-! ### The schedule -/

def blk (u : Vertex) : List Edge :=
  (List.finRange 910).filter fun q => decide (q ∈ physical ∧ tail q = u)

theorem schedule_eq : schedule = processingOrder.flatMap blk := rfl

attribute [local irreducible] schedule

theorem mem_blk {q : Edge} {u : Vertex} : q ∈ blk u ↔ q ∈ physical ∧ tail q = u := by
  simp [blk]

theorem mem_schedule (q : Edge) : q ∈ schedule ↔ q ∈ physical := by
  rw [schedule_eq, List.mem_flatMap]
  constructor
  · rintro ⟨u, -, hu⟩; exact (mem_blk.1 hu).1
  · intro h; exact ⟨tail q, mem_order _, mem_blk.2 ⟨h, rfl⟩⟩

theorem nodup_schedule : schedule.Nodup := by
  rw [schedule_eq, List.nodup_flatMap]
  refine ⟨fun u _ => (List.nodup_finRange 910).filter _, nodup_order.imp ?_⟩
  intro u u' hne q hq hq'
  exact hne ((mem_blk.1 hq).2.symm.trans (mem_blk.1 hq').2)

theorem eventEdge_eq (t : Fin schedule.length) : eventEdge t = schedule[t.val] :=
  List.getD_eq_getElem _ _ t.2

theorem eventEdge_phys (t : Fin schedule.length) : eventEdge t ∈ physical := by
  rw [eventEdge_eq, ← mem_schedule]; exact List.getElem_mem _

theorem eventEdge_unique (q : Edge) (hq : q ∈ physical) :
    ∃! t : Fin schedule.length, eventEdge t = q := by
  obtain ⟨k, hk, hkq⟩ := List.mem_iff_getElem.1 ((mem_schedule q).2 hq)
  refine ⟨⟨k, hk⟩, by show eventEdge ⟨k, hk⟩ = q; rw [eventEdge_eq]; exact hkq, fun t ht => ?_⟩
  change eventEdge t = q at ht
  rw [eventEdge_eq, ← hkq] at ht
  exact Fin.ext ((nodup_schedule.getElem_inj_iff).1 ht)

theorem schedule_length : schedule.length = physical.card := by
  rw [← List.toFinset_card_of_nodup nodup_schedule]
  apply congrArg Finset.card
  ext q
  rw [List.mem_toFinset, mem_schedule]

theorem mem_take_pos {u : Vertex} {p : ℕ} (h : u ∈ processingOrder.take p) : position u < p := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 h
  rw [List.getElem_take]
  unfold position
  rw [nodup_order.idxOf_getElem]
  simp at hk; omega

theorem mem_drop_pos {u : Vertex} {p : ℕ} (h : u ∈ processingOrder.drop p) : p ≤ position u := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 h
  rw [List.getElem_drop]
  unfold position
  rw [nodup_order.idxOf_getElem]
  omega

theorem split_getD (A Bk : List Edge) (P : Edge → Prop) (hA : ∀ q ∈ A, P q)
    (hB : ∀ q ∈ Bk, ¬ P q) (n : ℕ) (hn : n < (A ++ Bk).length) :
    P ((A ++ Bk).getD n 0) ↔ n < A.length := by
  rw [List.getD_eq_getElem _ _ hn]
  by_cases hlt : n < A.length
  · rw [List.getElem_append_left hlt]
    exact iff_of_true (hA _ (List.getElem_mem hlt)) hlt
  · rw [List.getElem_append_right (by omega)]
    rw [List.length_append] at hn
    exact iff_of_false (hB _ (List.getElem_mem (by omega))) hlt

/-- Events are scheduled block by block along the processing order. -/
theorem order_lemma (a t : Fin schedule.length)
    (h : position (tail (eventEdge a)) < position (tail (eventEdge t))) : a.val < t.val := by
  generalize hp : position (tail (eventEdge t)) = p at h
  have hs : schedule = (processingOrder.take p).flatMap blk ++
      (processingOrder.drop p).flatMap blk := by
    rw [schedule_eq, ← List.flatMap_append, List.take_append_drop]
  have hA : ∀ q ∈ (processingOrder.take p).flatMap blk, position (tail q) < p := by
    intro q hq
    obtain ⟨u, hu, hq⟩ := List.mem_flatMap.1 hq
    rw [(mem_blk.1 hq).2]; exact mem_take_pos hu
  have hB : ∀ q ∈ (processingOrder.drop p).flatMap blk, ¬ position (tail q) < p := by
    intro q hq
    obtain ⟨u, hu, hq⟩ := List.mem_flatMap.1 hq
    rw [(mem_blk.1 hq).2]; exact not_lt.2 (mem_drop_pos hu)
  have key : ∀ i : Fin schedule.length, (position (tail (eventEdge i)) < p ↔
      i.val < ((processingOrder.take p).flatMap blk).length) := by
    rintro ⟨n, hn⟩
    have hn' : n < ((processingOrder.take p).flatMap blk ++
      (processingOrder.drop p).flatMap blk).length := hs ▸ hn
    have he : eventEdge ⟨n, hn⟩ = ((processingOrder.take p).flatMap blk ++
        (processingOrder.drop p).flatMap blk).getD n 0 := by
      show schedule.getD n 0 = _
      rw [hs]
    rw [he]
    exact split_getD _ _ (fun q => position (tail q) < p) hA hB n hn'
  have ha := (key a).1 h
  have ht : ¬ (t.val < ((processingOrder.take p).flatMap blk).length) :=
    fun h' => lt_irrefl p (hp ▸ (key t).2 h')
  omega

/-! ### Linearity -/

noncomputable def toInputL : IndexInput →ₗ[F9] Input := LinearMap.funLeft F9 F9 sessionEquiv.symm

noncomputable def dvLin (v : Vertex) (q : Edge) :
    (Own network (fun _ => F9) v ×
      ((t : {t : Fin schedule.length // later (eventEdge t) = v}) → F9)) →ₗ[F9] F9 where
  toFun p := decoderValues v p.1 p.2 q
  map_add' p p' := by
    unfold decoderValues
    dsimp only
    split_ifs <;> simp
  map_smul' c p := by
    unfold decoderValues
    dsimp only
    split_ifs <;> simp

/-! ### Causality -/

theorem causal_core (t : Fin schedule.length) (m m' : IndexInput)
    (hown : ∀ i, earlier (sessionEquiv i).val = earlier (eventEdge t) → m i = m' i)
    (hrec : ∀ a : Fin schedule.length, a.val < t.val →
      later (eventEdge a) = earlier (eventEdge t) →
      execution (toInput m) (eventEdge a) = execution (toInput m') (eventEdge a)) :
    execution (toInput m) (eventEdge t) = execution (toInput m') (eventEdge t) := by
  have he := eventEdge_phys t
  have hnd := not_deleted_of_physical he
  have h1 := exec_local (toInput m) (eventEdge t)
  have h2 := exec_local (toInput m') (eventEdge t)
  obtain ⟨-, L, -, hL2⟩ := LI (tail (eventEdge t))
  rw [hL2] at h1 h2
  refine h1.trans (Eq.trans ?_ h2.symm)
  refine congrArg (fun z => localEvaluation (tail (eventEdge t)) (L z) (eventEdge t))
    (funext fun qq => ?_)
  obtain ⟨q, hq⟩ := qq
  have hq' := (Finset.mem_filter.1 hq).2
  show available _ (toInput m) _ q = available _ (toInput m') _ q
  unfold available
  by_cases hC : q ∈ C
  · rw [if_pos hC, if_pos hC]
  rw [if_neg hC, if_neg hC]
  by_cases hB : q ∈ B
  · have hh : head q = tail (eventEdge t) := by
      rcases hq' with ⟨hph, _⟩ | ⟨_, hh⟩ | ⟨hc, _⟩
      · exact absurd hph (not_physical_of_B hB)
      · exact hh
      · exact absurd hc hC
    rw [dif_pos hB, dif_pos hB, if_pos hh, if_pos hh]
    apply hown
    rw [Equiv.apply_symm_apply]
    show earlier q = earlier (eventEdge t)
    rw [← head_of_del (del_of_B hB), hh, tail_of_nd hnd]
  · rw [dif_neg hB, dif_neg hB]
    obtain ⟨hph, hh⟩ : q ∈ physical ∧ head q = tail (eventEdge t) := by
      rcases hq' with h | ⟨hb, _⟩ | ⟨hc, _⟩
      · exact h
      · exact absurd hb hB
      · exact absurd hc hC
    obtain ⟨a, ha, -⟩ := eventEdge_unique q hph
    have hlt : a.val < t.val := by
      apply order_lemma
      rw [ha, ← hh]
      exact pos_tail_lt q (not_deleted_of_physical hph)
    have := hrec a hlt (by
      rw [ha, ← head_of_nd (not_deleted_of_physical hph), hh, tail_of_nd hnd])
    rw [ha] at this
    exact this

/-! ### Correctness -/

theorem decoder_known (m : IndexInput) (v : Vertex) (own : Own network (fun _ => F9) v)
    (hist : (t : {t : Fin schedule.length // later (eventEdge t) = v}) → F9)
    (hown : ∀ j (h : network.s j = v), own ⟨j, h⟩ = m j)
    (hhist : ∀ s, hist s = execution (toInput m) (eventEdge s.val))
    (p : Edge) (hp : p ∈ knownPositions v) :
    decoderValues v own hist p = (eqv.symm (toInput m)).val p := by
  have hp' := (Finset.mem_filter.1 hp).2
  unfold decoderValues
  by_cases hC : p ∈ C
  · rw [if_pos hC, WC_C _ p hC]
  rewrite [if_neg hC]
  by_cases hB : p ∈ B
  · have hh : head p = v := by
      rcases hp' with ⟨hph, _⟩ | ⟨_, hh⟩ | ⟨hc, _⟩
      · exact absurd hph (not_physical_of_B hB)
      · exact hh
      · exact absurd hc hC
    have hs : network.s (sessionEquiv.symm ⟨p, hB⟩) = v := by
      show earlier (sessionEquiv (sessionEquiv.symm ⟨p, hB⟩)).val = _
      rw [Equiv.apply_symm_apply, ← head_of_del (del_of_B hB), hh]
    rewrite [dif_pos hB]
    dsimp only
    rewrite [dif_pos hs]
    exact (hown _ hs).trans (restr_symm (toInput m) ⟨p, hB⟩).symm
  · rewrite [dif_neg hB]
    have hph : p ∈ physical := by
      rcases hp' with h | h | h
      · exact h.1
      · exact absurd h.1 hB
      · exact absurd h.1 hC
    have hh : head p = v := by
      rcases hp' with h | h | h
      · exact h.2
      · exact absurd h.1 hB
      · exact absurd h.1 hC
    have hex : ∃ t : Fin schedule.length, eventEdge t = p ∧ later (eventEdge t) = v := by
      obtain ⟨a, ha, -⟩ := eventEdge_unique p hph
      exact ⟨a, ha, by rw [ha, ← head_of_nd (not_deleted_of_physical hph), hh]⟩
    rewrite [dif_pos hex, hhist, (Classical.choose_spec hex).1, exec_eq]
    rfl

/-- Stated as a function equality: the pointwise form makes the kernel unfold `execution`. -/
theorem received_eq (v : Vertex) (m : IndexInput) :
    (received protocol v m : {t : Fin schedule.length // later (eventEdge t) = v} → F9) =
      fun s => execution (toInput m) (eventEdge s.val) := rfl

theorem correct_core (m : IndexInput) (i : Fin network.k) :
    localEvaluation (network.t i)
      (interpolate (network.t i) (decoderValues (network.t i) (ownValues (network.t i) m)
        (received protocol (network.t i) m))) (sessionEquiv i).val = m i := by
  have hdel := del_of_B (sessionEquiv i).prop
  have hinc : incident (network.t i) (sessionEquiv i).val := by
    rw [network_t, ← tail_of_del hdel]; exact incident_tail _
  refine Eq.trans (det (WC_W (eqv.symm (toInput m))) (network.t i) _
    (decoder_known m (network.t i) (ownValues (network.t i) m) (received protocol (network.t i) m)
      (fun _ _ => rfl) (congrFun (received_eq (network.t i) m))) _ hinc) ?_
  rw [restr_symm (toInput m) (sessionEquiv i)]
  exact congrArg m (sessionEquiv.symm_apply_apply i)

end MultipleUnicast.Counterexample.Dev.CRCode

namespace MultipleUnicast.Counterexample.Dev.CR
open MultipleUnicast.Counterexample Dev.CRCode
open MultipleUnicast.Counterexample.Dev.RIGlobal

attribute [local irreducible] execution schedule earlier later edgePair incidenceList
  processingOrder deleted physical C B

theorem causalLinearCode : CausalLinearCode := by
  refine ⟨LI, fun t m m' h1 h2 =>
      causal_core t m m' h1 h2, ?phys, fun m i => correct_core m i,
    schedule_length, eventEdge_phys, eventEdge_unique, ?tlin, ?dlin⟩
  case phys =>
    intro t
    have he := eventEdge_phys t
    refine ⟨earlier_ne_later _, ?_⟩
    show (0 : ℝ) < network.C (earlier (eventEdge t)) (later (eventEdge t))
    rw [network_C, if_pos (adj_earlier_later he)]
    exact one_pos
  case tlin =>
    intro t
    refine ⟨(LinearMap.proj (eventEdge t)) ∘ₗ WC.subtype ∘ₗ eqv.symm.toLinearMap ∘ₗ toInputL,
      fun x => ?_⟩
    show execution (toInput x) (eventEdge t) = (eqv.symm (toInput x)).val (eventEdge t)
    exact congrFun (exec_eq _) _
  case dlin =>
    intro i
    obtain ⟨-, L, -, hL2⟩ := LI (network.t i)
    refine ⟨(LinearMap.proj (sessionEquiv i).val) ∘ₗ localEvaluation (network.t i) ∘ₗ L ∘ₗ
      LinearMap.pi (fun q : {q : Edge // q ∈ knownPositions (network.t i)} =>
        dvLin (network.t i) q.val), fun o h => ?_⟩
    show localEvaluation (network.t i)
      (interpolate (network.t i) (decoderValues (network.t i) o h)) (sessionEquiv i).val = _
    exact congrArg (fun z => localEvaluation (network.t i) z (sessionEquiv i).val) (hL2 _)

end MultipleUnicast.Counterexample.Dev.CR
end

section
set_option autoImplicit false
set_option maxRecDepth 2048
set_option Elab.async false

namespace MultipleUnicast.Counterexample.Dev.CRRate
open MultipleUnicast.Counterexample
open scoped Classical

/-! ### General entropy facts -/

theorem sum_toReal {A : Type} [Fintype A] (p : PMF A) : ∑ a, (p a).toReal = 1 := by
  have h : ∑ a, p a = 1 := by
    rw [← p.tsum_coe]; exact (tsum_fintype (L := SummationFilter.unconditional A) _).symm
  rw [← ENNReal.toReal_sum (fun a _ => p.apply_ne_top a), h]
  simp

theorem term_eq (x : ℝ) : -x * Real.logb 2 x = Real.negMulLog x / Real.log 2 := by
  simp only [Real.negMulLog, Real.logb]; ring

/-- Entropy of a law on a finite alphabet is at most `log₂` of its cardinality. -/
theorem entropy_le_card {A : Type} [Fintype A] (p : PMF A) :
    entropy p ≤ ENNReal.ofReal (Real.logb 2 (Fintype.card A)) := by
  have hne : Nonempty A := let ⟨a, _⟩ := p.support_nonempty; ⟨a⟩
  unfold entropy
  rw [tsum_fintype]
  simp_rw [term_eq]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => div_nonneg
    (Real.negMulLog_nonneg ENNReal.toReal_nonneg
      (ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using p.coe_le_one a)))
    (Real.log_nonneg one_le_two))]
  apply ENNReal.ofReal_le_ofReal
  rw [← Finset.sum_div, Real.logb]
  apply div_le_div_of_nonneg_right _ (Real.log_pos one_lt_two).le
  have hn : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have J := Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ)
    (w := fun _ => 1 / (Fintype.card A : ℝ)) (p := fun a => (p a).toReal)
    (fun _ _ => by positivity) (by simp [Finset.card_univ])
    (fun _ _ => Set.mem_Ici.2 ENNReal.toReal_nonneg)
  simp only [smul_eq_mul, ← Finset.mul_sum, sum_toReal, mul_one] at J
  have h2 : Real.negMulLog (1 / (Fintype.card A : ℝ)) =
      1 / (Fintype.card A : ℝ) * Real.log (Fintype.card A) := by
    simp [Real.negMulLog, Real.log_inv]
  rw [h2] at J
  exact le_of_mul_le_mul_left J (by positivity)

theorem entropy_map_equiv {A B : Type} (p : PMF A) (e : A ≃ B) :
    entropy (p.map e) = entropy p := by
  unfold entropy
  have h : ∀ b, (p.map e) b = p (e.symm b) := by
    intro b
    rw [PMF.map_apply]
    rw [tsum_eq_single (e.symm b)]
    · simp
    · intro a ha
      rw [if_neg]
      intro hb
      exact ha (by rw [hb, Equiv.symm_apply_apply])
  simp_rw [h]
  exact e.symm.tsum_eq (fun a => ENNReal.ofReal (-(p a).toReal * Real.logb 2 (p a).toReal))

theorem entropy_le_equiv {A B : Type} [Fintype B] (p : PMF A) (e : A ≃ B) :
    entropy p ≤ ENNReal.ofReal (Real.logb 2 (Fintype.card B)) := by
  rw [← entropy_map_equiv p e]
  exact entropy_le_card _

/-- Entropy of the uniform law on a finite alphabet. -/
theorem entropy_uniform {A : Type} [Fintype A] [Nonempty A] :
    entropy (PMF.uniformOfFintype A) = ENNReal.ofReal (Real.logb 2 (Fintype.card A)) := by
  unfold entropy
  rw [tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hn.le]
  congr 1
  rw [Real.logb_inv]
  field_simp

/-- Marginals of the uniform law on a product are uniform. -/
theorem uniform_marginal {ι α : Type} [Fintype ι] [DecidableEq ι] [Fintype α] [Nonempty α] (i : ι) :
    (PMF.uniformOfFintype (ι → α)).map (fun x => x i) = PMF.uniformOfFintype α := by
  ext a
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
    PMF.toOuterMeasure_uniformOfFintype_apply, PMF.uniformOfFintype_apply]
  set S := (fun x : ι → α => x i) ⁻¹' {a}
  let e : S × α ≃ (ι → α) :=
    { toFun := fun p => Function.update p.1.val i p.2
      invFun := fun m => (⟨Function.update m i a, by simp [S]⟩, m i)
      left_inv := by
        rintro ⟨⟨m, hm⟩, b⟩
        have hm' : m i = a := hm
        ext
        · simp [← hm']
        · simp
      right_inv := by intro m; simp }
  have hc := Fintype.card_congr e
  rw [Fintype.card_prod] at hc
  rw [← hc]
  have hS : (Fintype.card S : ENNReal) ≠ 0 := by
    have : Nonempty S := ⟨⟨fun _ => a, rfl⟩⟩
    exact_mod_cast Fintype.card_ne_zero
  push_cast
  rw [← one_div, ← ENNReal.mul_div_mul_left 1 (Fintype.card α : ENNReal) hS
    (ENNReal.natCast_ne_top _), mul_one]

/-! ### The concrete alphabet and law -/

theorem card_F9 : Fintype.card F9 = 9 := by
  rw [Fintype.ofEquiv_card]; simp

theorem k_eq : network.k = 157 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hB, -⟩ := balanced_orientation
  have hk : network.k = Fintype.card Session := by simp only [network]
  rw [hk, Fintype.card_coe, hB]

theorem marginal (i : Fin network.k) :
    witnessLaw.map (fun m => m i) = PMF.uniformOfFintype F9 := by
  unfold witnessLaw; exact uniform_marginal i

theorem independent : IndependentSources (M := fun _ => F9) witnessLaw := by
  intro m
  simp only [marginal, PMF.uniformOfFintype_apply]
  show (PMF.uniformOfFintype IndexInput) m = _
  rw [PMF.uniformOfFintype_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Fintype.card_fun, Fintype.card_fin, card_F9, k_eq, ← ENNReal.inv_pow]
  rw [Nat.cast_pow, Nat.cast_ofNat]

theorem marginal_entropy (i : Fin network.k) :
    ENNReal.ofReal (1 * network.D i * witnessScale) ≤ entropy (witnessLaw.map (fun m => m i)) := by
  rw [marginal, entropy_uniform, card_F9]
  show ENNReal.ofReal (1 * 1 * Real.logb 2 9) ≤ _
  simp

/-! ### Arc counting -/

theorem pointEnd_lt (q : Edge) : (pointEnd q).val < 91 := (edgePair q).1.isLt

theorem lineEnd_ge (q : Edge) : 91 ≤ (lineEnd q).val := by
  simp [lineEnd]

theorem ends_inj {q q' : Edge} (hp : pointEnd q = pointEnd q') (hl : lineEnd q = lineEnd q') :
    q = q' := by
  apply (balanced_orientation.2.2.1)
  have hp' := congrArg Fin.val hp
  have hl' := congrArg Fin.val hl
  simp only [pointEnd, lineEnd] at hp' hl'
  exact Prod.ext (Fin.ext hp') (Fin.ext (by omega))

theorem eq_of_sym {q q' : Edge} (h : s(pointEnd q, lineEnd q) = s(pointEnd q', lineEnd q')) :
    q = q' := by
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ends_inj h1 h2
  · have a := congrArg Fin.val h1
    have := pointEnd_lt q
    have := lineEnd_ge q'
    omega

theorem sym_ends (q : Edge) : s(earlier q, later q) = s(pointEnd q, lineEnd q) := by
  unfold earlier later
  split_ifs
  · rfl
  · exact Sym2.eq_swap

theorem hlen : protocol.length = schedule.length := by simp only [protocol]

/-- The physical edge carried by an event of the protocol. -/
noncomputable def ev (t : Fin protocol.length) : Edge := eventEdge (Fin.cast hlen t)

theorem src_eq (t : Fin protocol.length) : protocol.src t = earlier (ev t) := by
  dsimp only [protocol, ev, eventEdge, Fin.cast]

theorem dst_eq (t : Fin protocol.length) : protocol.dst t = later (ev t) := by
  dsimp only [protocol, ev, eventEdge, Fin.cast]

theorem event_inj {t t' : Fin protocol.length}
    (h : s(protocol.src t, protocol.dst t) = s(protocol.src t', protocol.dst t')) : t = t' := by
  rw [src_eq, src_eq, dst_eq, dst_eq, sym_ends, sym_ends] at h
  have hq : ev t = ev t' := eq_of_sym h
  obtain ⟨s, _, hs⟩ := Dev.CR.causalLinearCode.2.2.2.2.2.2.1 (ev t')
    (Dev.CR.causalLinearCode.2.2.2.2.2.1 (Fin.cast hlen t'))
  exact Fin.cast_injective hlen ((hs _ hq).trans (hs _ rfl).symm)

theorem adj_of_event (t : Fin protocol.length) : graph.Adj (protocol.src t) (protocol.dst t) := by
  have h := (Dev.CR.causalLinearCode.2.2.1 t).2
  by_contra hn
  have : network.C (protocol.src t) (protocol.dst t) = 0 := by
    show (if graph.Adj _ _ then (1 : ℝ) else 0) = 0
    rw [if_neg hn]
  rw [this] at h
  exact lt_irrefl _ h

abbrev Arc (u v : Vertex) := {t : Fin protocol.length // protocol.src t = u ∧ protocol.dst t = v}

theorem arc_card (u v : Vertex) :
    ((Fintype.card (Arc u v) : ℝ) + Fintype.card (Arc v u)) ≤ network.C u v := by
  have hsub : Subsingleton (Arc u v ⊕ Arc v u) := ⟨by
    rintro (⟨a, ha⟩ | ⟨a, ha⟩) (⟨b, hb⟩ | ⟨b, hb⟩)
    · exact congrArg Sum.inl (Subtype.ext (event_inj (by rw [ha.1, ha.2, hb.1, hb.2])))
    · have := event_inj (t := a) (t' := b) (by rw [ha.1, ha.2, hb.1, hb.2]; exact Sym2.eq_swap)
      subst this
      exact absurd (hb.1.trans ha.2.symm) (Dev.CR.causalLinearCode.2.2.1 a).1
    · have := event_inj (t := a) (t' := b) (by rw [ha.1, ha.2, hb.1, hb.2]; exact Sym2.eq_swap)
      subst this
      exact absurd (hb.1.trans ha.2.symm) (Dev.CR.causalLinearCode.2.2.1 a).1
    · exact congrArg Sum.inr (Subtype.ext (event_inj (by rw [ha.1, ha.2, hb.1, hb.2])))⟩
  have h1 : Fintype.card (Arc u v) + Fintype.card (Arc v u) ≤ 1 := by
    rw [← Fintype.card_sum]; exact Fintype.card_le_one_iff_subsingleton.2 hsub
  by_cases hadj : graph.Adj u v
  · have : network.C u v = 1 := by
      show (if graph.Adj u v then (1 : ℝ) else 0) = 1
      rw [if_pos hadj]
    rw [this]
    exact_mod_cast h1
  · have e1 : Fintype.card (Arc u v) = 0 := Fintype.card_eq_zero_iff.2 ⟨fun ⟨t, ht⟩ =>
      hadj (by have := adj_of_event t; rwa [ht.1, ht.2] at this)⟩
    have e2 : Fintype.card (Arc v u) = 0 := Fintype.card_eq_zero_iff.2 ⟨fun ⟨t, ht⟩ =>
      hadj (by have := adj_of_event t; rw [ht.1, ht.2] at this; exact this.symm)⟩
    rw [e1, e2]
    simpa using network.C_nonneg u v

theorem alphabet_eq (t : Fin protocol.length) : protocol.alphabet t = F9 := by
  dsimp only [protocol]

theorem arc_entropy (u v : Vertex) :
    entropy (witnessLaw.map (arcSymbols protocol u v)) ≤
      ENNReal.ofReal (Fintype.card (Arc u v) * Real.logb 2 9) := by
  let e : ((t : Arc u v) → protocol.alphabet t.val) ≃ (Arc u v → F9) :=
    Equiv.piCongrRight (fun t => Equiv.cast (alphabet_eq t.val))
  refine (entropy_le_equiv _ e).trans (le_of_eq ?_)
  congr 1
  rw [Fintype.card_fun, card_F9]
  push_cast
  rw [Real.logb_pow]

theorem arc_bound (u v : Vertex) :
    entropy (witnessLaw.map (arcSymbols protocol u v)) +
      entropy (witnessLaw.map (arcSymbols protocol v u)) ≤
      ENNReal.ofReal (network.C u v * witnessScale) := by
  have hL : 0 ≤ Real.logb 2 9 := Real.logb_nonneg one_lt_two (by norm_num)
  refine (add_le_add (arc_entropy u v) (arc_entropy v u)).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← add_mul]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (arc_card u v) hL)

theorem scale_pos : 0 < witnessScale := Real.logb_pos one_lt_two (by norm_num)

theorem supports : SupportsRate protocol witnessLaw 1 witnessScale := by
  obtain ⟨-, hC, hU, hR, -⟩ := Dev.CR.causalLinearCode
  exact ⟨zero_le_one, scale_pos, independent, hC, hU, hR, marginal_entropy, arc_bound⟩

end MultipleUnicast.Counterexample.Dev.CRRate

namespace MultipleUnicast.Counterexample
open Dev.CRRate

theorem chk_coding_rate :
    network.k = 157 ∧ CausalLinearCode ∧
    0 < witnessScale ∧ SupportsRate protocol witnessLaw 1 witnessScale ∧
    (1 : ENNReal) ≤ codingThroughput network := by
  refine ⟨k_eq, Dev.CR.causalLinearCode, scale_pos, supports, ?_⟩
  exact le_sSup ⟨fun _ => F9, protocol, witnessLaw, 1, witnessScale, supports, by simp⟩

end MultipleUnicast.Counterexample
end

theorem solution : type_of% @MultipleUnicast.Counterexample.chk_coding_rate := @MultipleUnicast.Counterexample.chk_coding_rate
