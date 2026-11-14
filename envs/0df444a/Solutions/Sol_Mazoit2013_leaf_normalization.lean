-- Prove2me | solution 1 for Mazoit2013.leaf_normalization
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-14T01:22:35.628364+00:00
-- url     : https://prove2.me/submissions/806cbb99-5ef7-4647-a396-8e4748e4b33b

import Definitions.Def_Mazoit2013_PartialDecompositions
open RobertsonSeymour1986.GM5 StableMSR.Recovery.Havens StableMSR.Recovery.PartialDecompositions
namespace StableMSR.Recovery.PartialDecompositions
variable {V : Type} [Fintype V] [DecidableEq V]
lemma flap_nonempty {T : Type} {G : SimpleGraph V} {b : ℕ} {tree : SimpleGraph T}
    {bags : T → Finset V} (h : IsPartial G b tree bags) {C : Finset V}
    (hC : C ∈ flaps b tree bags) : C.Nonempty := by
  obtain ⟨t,u,hbig,htu,rfl⟩ := mem_flaps.mp hC
  obtain ⟨v,_,hv,hunique⟩ := h.2.2 t hbig
  have huv := hunique u htu
  subst u
  apply Finset.sdiff_nonempty.mpr
  intro hsub
  have := Finset.card_le_card hsub
  omega
end StableMSR.Recovery.PartialDecompositions
open RobertsonSeymour1986.GM5 StableMSR.Recovery.Havens
namespace StableMSR.Recovery.PartialDecompositions
variable {V T : Type} [DecidableEq V]
lemma leaf_neighbor_mem_walk {tree : SimpleGraph T} {t u s : T}
    (hunique : ∀ v, tree.Adj t v → v = u) (hne : t ≠ s)
    (p : tree.Walk t s) : u ∈ p.support := by
  cases p with
  | nil => exact False.elim (hne rfl)
  | @cons a v s htv p =>
    have hv := hunique v htv
    subst v
    simp
/-- A vertex in a leaf bag but not its neighbor bag occurs in no other bag. -/
theorem leaf_exclusive_only {G : SimpleGraph V} {tree : SimpleGraph T}
    {bags : T → Finset V} (hdec : IsTreeDecomposition G tree bags)
    {t u : T} (hunique : ∀ v, tree.Adj t v → v = u)
    {x : V} (hx : x ∈ bags t \ bags u) {s : T} (hxs : x ∈ bags s) : s = t := by
  classical
  by_contra hst
  obtain ⟨p,hp⟩ := hdec.1.connected.exists_isPath t s
  have hu : u ∈ p.support := leaf_neighbor_mem_walk hunique (Ne.symm hst) p
  have hxU := hdec.2.2.2 t u s p hp hu (Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hx).1,hxs⟩)
  exact (Finset.mem_sdiff.mp hx).2 hxU
/-- Every graph edge leaving a leaf flap reaches the neighbor bag. -/
theorem leaf_external_neighbor {G : SimpleGraph V} {tree : SimpleGraph T}
    {bags : T → Finset V} (hdec : IsTreeDecomposition G tree bags)
    {t u : T} (hunique : ∀ v, tree.Adj t v → v = u)
    {x y : V} (hx : x ∈ bags t \ bags u) (hxy : G.Adj x y)
    (hy : y ∉ bags t \ bags u) : y ∈ bags u := by
  obtain ⟨s,hxs,hys⟩ := hdec.2.2.1 x y hxy
  have hs := leaf_exclusive_only hdec hunique hx hxs
  subst s
  by_contra hyu
  exact hy (Finset.mem_sdiff.mpr ⟨hys,hyu⟩)
/-- The external boundary of a leaf flap is contained in the adhesion to its neighbor. -/
theorem leaf_external_neighbor_adhesion {G : SimpleGraph V} {tree : SimpleGraph T}
    {bags : T → Finset V} (hdec : IsTreeDecomposition G tree bags)
    {t u : T} (hunique : ∀ v, tree.Adj t v → v = u)
    {x y : V} (hx : x ∈ bags t \ bags u) (hxy : G.Adj x y)
    (hy : y ∉ bags t \ bags u) : y ∈ bags t ∩ bags u := by
  obtain ⟨s,hxs,hys⟩ := hdec.2.2.1 x y hxy
  have hs := leaf_exclusive_only hdec hunique hx hxs
  subst s
  exact Finset.mem_inter.mpr ⟨hys,leaf_external_neighbor hdec hunique hx hxy hy⟩
/-- Every realized flap has a small separator containing all of its external neighbors. -/
theorem partial_flap_has_separator [Fintype V] {G : SimpleGraph V} {b : ℕ}
    {tree : SimpleGraph T} {bags : T → Finset V}
    (h : IsPartial G b tree bags) {C : Finset V} (hC : C ∈ flaps b tree bags) :
    ∃ S : Finset V, S.card ≤ b ∧ Disjoint C S ∧
      ∀ x ∈ C, ∀ y, G.Adj x y → y ∉ C → y ∈ S := by
  obtain ⟨t,u,hbig,htu,rfl⟩ := mem_flaps.mp hC
  obtain ⟨v,htv,hsmall,hunique⟩ := h.2.2 t hbig
  have huv := hunique u htu
  subst u
  refine ⟨bags t ∩ bags v,?_,?_,?_⟩
  · exact le_trans (Finset.card_le_card Finset.inter_subset_right) hsmall
  · apply Finset.disjoint_left.mpr
    intro x hx hxi
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_inter.mp hxi).2
  · intro x hx y hxy hy
    exact leaf_external_neighbor_adhesion h.1 hunique hx hxy hy
/-- A realized flap admits a separator no larger than the common threshold. -/
theorem realizable_flap_has_separator [Fintype V] {G : SimpleGraph V} {b : ℕ}
    {d : Finset (Finset V)} (hd : RealizableFlaps G b d) {C : Finset V} (hC : C ∈ d) :
    ∃ S : Finset V, S.card ≤ b ∧ Disjoint C S ∧
      ∀ x ∈ C, ∀ y, G.Adj x y → y ∉ C → y ∈ S := by
  obtain ⟨T,_,tree,bags,h,rfl⟩ := hd
  exact partial_flap_has_separator h hC
/-- A leaf can occur on a simple path only as an endpoint. -/
theorem leaf_mem_path_endpoints {tree : SimpleGraph T} {t u s v : T}
    (hunique : ∀ z, tree.Adj t z → z = u) (p : tree.Walk s v)
    (hp : p.IsPath) (ht : t ∈ p.support) : t = s ∨ t = v := by
  induction p with
  | nil => exact Or.inl (by simpa using ht)
  | @cons a b c hab p ih =>
    by_cases hta : t = a
    · exact Or.inl hta
    have htp : t ∈ p.support := (List.mem_cons.mp ht).resolve_left hta
    have hpath : p.IsPath := by
      exact SimpleGraph.Walk.IsPath.mk' (List.nodup_cons.mp hp.support_nodup).2
    rcases ih hpath htp with htb | htc
    · subst b
      by_cases htc : t = c
      · exact Or.inr htc
      have hau : a = u := hunique a hab.symm
      have hup := leaf_neighbor_mem_walk hunique htc p
      have hap : a ∈ p.support := hau ▸ hup
      exact False.elim ((List.nodup_cons.mp hp.support_nodup).1 hap)
    · exact Or.inr htc
/-- Shrinking a leaf to a subset that retains its flap and boundary preserves the decomposition. -/
theorem shrink_leaf_decomposition [DecidableEq T] {G : SimpleGraph V} {tree : SimpleGraph T}
    {bags : T → Finset V} (hdec : IsTreeDecomposition G tree bags)
    {t u : T} (htu : tree.Adj t u) (hunique : ∀ v, tree.Adj t v → v = u)
    (B : Finset V) (hB : B ⊆ bags t) (hflap : bags t \ bags u ⊆ B)
    (hboundary : ∀ x ∈ bags t \ bags u, ∀ y, G.Adj x y → y ∈ B) :
    IsTreeDecomposition G tree (Function.update bags t B) := by
  classical
  have htu' : t ≠ u := htu.ne
  have hsub : ∀ s, Function.update bags t B s ⊆ bags s := by
    intro s
    by_cases hs : s = t
    · subst s; simpa using hB
    · simp [Function.update_of_ne hs]
  refine ⟨hdec.1,?_,?_,?_⟩
  · intro x
    obtain ⟨s,hx⟩ := hdec.2.1 x
    by_cases hs : s = t
    · subst s
      by_cases hxu : x ∈ bags u
      · exact ⟨u,by simpa [Function.update_of_ne htu'.symm] using hxu⟩
      · exact ⟨t,by simpa using hflap (Finset.mem_sdiff.mpr ⟨hx,hxu⟩)⟩
    · exact ⟨s,by simpa [Function.update_of_ne hs] using hx⟩
  · intro x y hxy
    obtain ⟨s,hxs,hys⟩ := hdec.2.2.1 x y hxy
    by_cases hs : s = t
    · subst s
      by_cases hxu : x ∈ bags u
      · by_cases hyu : y ∈ bags u
        · exact ⟨u,by simpa [Function.update_of_ne htu'.symm] using hxu,
            by simpa [Function.update_of_ne htu'.symm] using hyu⟩
        · have hyC := Finset.mem_sdiff.mpr ⟨hys,hyu⟩
          exact ⟨t,by simpa using hboundary y hyC x hxy.symm,by simpa using hflap hyC⟩
      · have hxC := Finset.mem_sdiff.mpr ⟨hxs,hxu⟩
        exact ⟨t,by simpa using hflap hxC,by simpa using hboundary x hxC y hxy⟩
    · exact ⟨s,by simpa [Function.update_of_ne hs] using hxs,
        by simpa [Function.update_of_ne hs] using hys⟩
  · intro s v r p hp hv x hx
    obtain ⟨hxs,hxr⟩ := Finset.mem_inter.mp hx
    by_cases hvt : v = t
    · subst v
      rcases leaf_mem_path_endpoints hunique p hp hv with hts | htr
      · subst s; exact hxs
      · subst r; exact hxr
    · have hxv := hdec.2.2.2 s v r p hp hv (Finset.mem_inter.mpr ⟨hsub s hxs,hsub r hxr⟩)
      simpa [Function.update_of_ne hvt] using hxv
/-- Leaf shrinking retains the partial-decomposition threshold. -/
theorem shrink_leaf_partial [Fintype V] [DecidableEq T]
    {G : SimpleGraph V} {b : ℕ} {tree : SimpleGraph T} {bags : T → Finset V}
    (h : IsPartial G b tree bags) {t u : T} (hbig : b < (bags t).card)
    (htu : tree.Adj t u) (B : Finset V) (hB : B ⊆ bags t)
    (hflap : bags t \ bags u ⊆ B)
    (hboundary : ∀ x ∈ bags t \ bags u, ∀ y, G.Adj x y → y ∈ B) :
    IsPartial G b tree (Function.update bags t B) := by
  classical
  obtain ⟨v,htv,hsmall,hunique⟩ := h.2.2 t hbig
  have huv := hunique u htu
  subst u
  have hsub : ∀ s, Function.update bags t B s ⊆ bags s := by
    intro s
    by_cases hs : s = t
    · subst s; simpa using hB
    · simp [Function.update_of_ne hs]
  refine ⟨shrink_leaf_decomposition h.1 htv hunique B hB hflap hboundary,?_,?_⟩
  · obtain ⟨s,hs⟩ := h.2.1
    exact ⟨s,le_trans (Finset.card_le_card (hsub s)) hs⟩
  · intro s hs
    have hsbig : b < (bags s).card := lt_of_lt_of_le hs (Finset.card_le_card (hsub s))
    obtain ⟨r,hsr,hr,huniq⟩ := h.2.2 s hsbig
    refine ⟨r,hsr,le_trans (Finset.card_le_card (hsub r)) hr,huniq⟩
/-- Shrinking a large leaf creates no new flap. -/
theorem shrink_leaf_flaps_subset [Fintype V] [DecidableEq T]
    {G : SimpleGraph V} {b : ℕ} {tree : SimpleGraph T} {bags : T → Finset V}
    (h : IsPartial G b tree bags) {t u : T} (hbig : b < (bags t).card)
    (htu : tree.Adj t u) (B : Finset V) (hB : B ⊆ bags t)
    (hflap : bags t \ bags u ⊆ B) :
    flaps b tree (Function.update bags t B) ⊆ flaps b tree bags := by
  classical
  have hsub : ∀ s, Function.update bags t B s ⊆ bags s := by
    intro s
    by_cases hs : s = t
    · subst s; simpa using hB
    · simp [Function.update_of_ne hs]
  intro C hC
  obtain ⟨s,r,hsbig,hsr,rfl⟩ := mem_flaps.mp hC
  have hsold : b < (bags s).card := lt_of_lt_of_le hsbig (Finset.card_le_card (hsub s))
  obtain ⟨r',hsr',hr',huniq⟩ := h.2.2 s hsold
  have hrr' := huniq r hsr
  subst r'
  have hrt : r ≠ t := by intro hrt; subst r; omega
  by_cases hst : s = t
  · subst s
    have hur := huniq u htu
    subst r
    have heq : B \ bags u = bags t \ bags u := by
      apply Finset.Subset.antisymm
      · intro x hx
        exact Finset.mem_sdiff.mpr ⟨hB (Finset.mem_sdiff.mp hx).1,(Finset.mem_sdiff.mp hx).2⟩
      · intro x hx
        exact Finset.mem_sdiff.mpr ⟨hflap hx,(Finset.mem_sdiff.mp hx).2⟩
    simp only [Function.update_self, Function.update_of_ne hrt]
    rw [heq]
    exact mem_flaps.mpr ⟨t,u,hbig,htu,rfl⟩
  · simp only [Function.update_of_ne hst,Function.update_of_ne hrt]
    exact mem_flaps.mpr ⟨s,r,hsold,hsr,rfl⟩
/-- Every flap other than the selected leaf flap survives a leaf shrink. -/
theorem shrink_leaf_flaps_survive [Fintype V] [DecidableEq T]
    {G : SimpleGraph V} {b : ℕ} {tree : SimpleGraph T} {bags : T → Finset V}
    (h : IsPartial G b tree bags) {t u : T} (hbig : b < (bags t).card)
    (htu : tree.Adj t u) (B : Finset V) {C : Finset V}
    (hC : C ∈ flaps b tree bags) (hne : C ≠ bags t \ bags u) :
    C ∈ flaps b tree (Function.update bags t B) := by
  classical
  obtain ⟨s,r,hsbig,hsr,rfl⟩ := mem_flaps.mp hC
  obtain ⟨r',hsr',hr',huniq⟩ := h.2.2 s hsbig
  have hrr' := huniq r hsr
  subst r'
  have hrt : r ≠ t := by intro hrt; subst r; omega
  have hst : s ≠ t := by
    intro hst
    subst s
    have hur := huniq u htu
    subst r
    exact hne rfl
  refine mem_flaps.mpr ⟨s,r,?_,hsr,?_⟩
  · simpa [Function.update_of_ne hst] using hsbig
  · simp [Function.update_of_ne hst,Function.update_of_ne hrt]
end StableMSR.Recovery.PartialDecompositions
/-- Normalize a large leaf to its flap together with its external graph boundary.
The only flap this can remove is the selected flap; it removes that flap if the normalized bag is small. -/
theorem solution {V T : Type} [Fintype V] [DecidableEq V] [DecidableEq T]
    {G : SimpleGraph V} {b : ℕ} {tree : SimpleGraph T} {bags : T → Finset V}
    (h : IsPartial G b tree bags) {t u : T} (hbig : b < (bags t).card)
    (htu : tree.Adj t u) :
    ∃ B : Finset V,
      (∀ y, y ∈ B ↔ y ∈ bags t \ bags u ∨
        (y ∉ bags t \ bags u ∧ ∃ x ∈ bags t \ bags u, G.Adj x y)) ∧
      B ⊆ bags t ∧
      IsPartial G b tree (Function.update bags t B) ∧
      flaps b tree (Function.update bags t B) ⊆ flaps b tree bags ∧
      (∀ C ∈ flaps b tree bags, C ≠ bags t \ bags u →
        C ∈ flaps b tree (Function.update bags t B)) ∧
      (B.card ≤ b → bags t \ bags u ∉ flaps b tree (Function.update bags t B)) := by
  classical
  let C := bags t \ bags u
  let B := C ∪ Finset.univ.filter (fun y => y ∉ C ∧ ∃ x ∈ C, G.Adj x y)
  have hmem : ∀ y, y ∈ B ↔ y ∈ C ∨ (y ∉ C ∧ ∃ x ∈ C, G.Adj x y) := by
    intro y
    simp [B]
  obtain ⟨v,htv,hsmall,hunique⟩ := h.2.2 t hbig
  have huv := hunique u htu
  subst v
  have hCB : C ⊆ B := Finset.subset_union_left
  have hB : B ⊆ bags t := by
    intro y hy
    rcases (hmem y).mp hy with hy | ⟨hy, x,hx,hxy⟩
    · exact (Finset.mem_sdiff.mp hy).1
    · exact (Finset.mem_inter.mp (leaf_external_neighbor_adhesion h.1 hunique hx hxy hy)).1
  have hbnd : ∀ x ∈ C, ∀ y, G.Adj x y → y ∈ B := by
    intro x hx y hxy
    by_cases hy : y ∈ C
    · exact hCB hy
    · exact (hmem y).mpr (Or.inr ⟨hy,x,hx,hxy⟩)
  refine ⟨B,hmem,hB,shrink_leaf_partial h hbig htu B hB hCB hbnd,
    shrink_leaf_flaps_subset h hbig htu B hB hCB,?_,?_⟩
  · intro D hD hne
    exact shrink_leaf_flaps_survive h hbig htu B hD hne
  · intro hBsmall hC
    have hCorig : C ∈ flaps b tree bags := mem_flaps.mpr ⟨t,u,hbig,htu,rfl⟩
    obtain ⟨x,hx⟩ := flap_nonempty h hCorig
    obtain ⟨s,r,hsbig,hsr,hCeq⟩ := mem_flaps.mp hC
    have hst : s ≠ t := by
      intro hst
      subst s
      simp only [Function.update_self] at hsbig
      omega
    have hxs : x ∈ bags s := by
      have hxnew : x ∈ Function.update bags t B s \ Function.update bags t B r := hCeq ▸ hx
      simpa [Function.update_of_ne hst] using (Finset.mem_sdiff.mp hxnew).1
    exact hst (leaf_exclusive_only h.1 hunique hx hxs)
