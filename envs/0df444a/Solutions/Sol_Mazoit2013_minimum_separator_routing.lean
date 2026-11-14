-- Prove2me | solution 1 for Mazoit2013.minimum_separator_routing
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-14T01:22:46.27167+00:00
-- url     : https://prove2.me/submissions/86157fdf-db82-4ea2-88a4-2d06f2f62e7d

import Definitions.Def_Mazoit2013_RoutedBags
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
/-- Normalize a large leaf to its flap together with its external graph boundary.
The only flap this can remove is the selected flap; it removes that flap if the normalized bag is small. -/
theorem shrink_leaf_normalization [Fintype V] [DecidableEq T]
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
end StableMSR.Recovery.PartialDecompositions


/- Finite cardinal and flap-control facts for restricting bags to one side of a separation. -/
namespace StableMSR.Recovery.BagPullback
variable {V : Type} [DecidableEq V]

/-- Keep the old vertices on one side, and add the specified separator vertices. -/
def pullbackBag (B R A : Finset V) : Finset V := (B ∩ R) ∪ A

@[simp] lemma mem_pullbackBag {B R A : Finset V} {v : V} :
    v ∈ pullbackBag B R A ↔ (v ∈ B ∧ v ∈ R) ∨ v ∈ A := by
  simp [pullbackBag]

lemma pullbackBag_subset_side {B R A : Finset V} (hA : A ⊆ R) :
    pullbackBag B R A ⊆ R := by
  intro v hv
  rcases mem_pullbackBag.mp hv with ⟨_,hr⟩ | ha
  · exact hr
  · exact hA ha

lemma kept_subset_pullbackBag (B R A : Finset V) : B ∩ R ⊆ pullbackBag B R A :=
  Finset.subset_union_left

lemma added_subset_pullbackBag (B R A : Finset V) : A ⊆ pullbackBag B R A :=
  Finset.subset_union_right

/-- Only genuinely new vertices have to be charged to removed old vertices. -/
lemma pullbackBag_eq_new_union {B R A : Finset V} (hA : A ⊆ R) :
    pullbackBag B R A = (B ∩ R) ∪ (A \ B) := by
  ext v
  simp only [mem_pullbackBag,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
  constructor
  · rintro (h | ha)
    · exact Or.inl h
    · by_cases hb : v ∈ B
      · exact Or.inl ⟨hb,hA ha⟩
      · exact Or.inr ⟨ha,hb⟩
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr h.1

/-- A charging injection from new separator vertices into removed vertices prevents bag growth. -/
theorem card_pullbackBag_le {B R A : Finset V} (hA : A ⊆ R)
    (f : V → V) (hf : ∀ v ∈ A \ B, f v ∈ B \ R)
    (hinj : Set.InjOn f (A \ B : Finset V)) :
    (pullbackBag B R A).card ≤ B.card := by
  rw [pullbackBag_eq_new_union hA]
  have hc : (A \ B).card ≤ (B \ R).card := Finset.card_le_card_of_injOn f hf hinj
  have hu := Finset.card_union_le (B ∩ R) (A \ B)
  have hb := Finset.card_inter_add_card_sdiff B R
  omega

/-- The stronger charging hypothesis, often convenient for a supplied linkage. -/
theorem card_pullbackBag_le_of_all_added {B R A : Finset V}
    (f : V → V) (hf : ∀ v ∈ A, f v ∈ B \ R)
    (hinj : Set.InjOn f (A : Set V)) :
    (pullbackBag B R A).card ≤ B.card := by
  have hc : A.card ≤ (B \ R).card := Finset.card_le_card_of_injOn f hf hinj
  have hu := Finset.card_union_le (B ∩ R) A
  have hb := Finset.card_inter_add_card_sdiff B R
  change ((B ∩ R) ∪ A).card ≤ B.card
  omega

/-- If added leaf vertices also occur at its parent, its new flap is contained in the old flap. -/
theorem flap_subset_old {B N R A P : Finset V} (hAP : A ⊆ P) :
    pullbackBag B R A \ pullbackBag N R P ⊆ B \ N := by
  intro v hv
  obtain ⟨hvB,hvN⟩ := Finset.mem_sdiff.mp hv
  have hvA : v ∉ A := fun ha => hvN (mem_pullbackBag.mpr (Or.inr (hAP ha)))
  obtain ⟨hb,hr⟩ := (mem_pullbackBag.mp hvB).resolve_right hvA
  exact Finset.mem_sdiff.mpr ⟨hb,fun hn => hvN (mem_pullbackBag.mpr (Or.inl ⟨hn,hr⟩))⟩

/-- The new flap lies on the retained side whenever all added vertices do. -/
lemma flap_subset_side {B N R A P : Finset V} (hA : A ⊆ R) :
    pullbackBag B R A \ pullbackBag N R P ⊆ R :=
  fun _ hv => pullbackBag_subset_side hA (Finset.mem_sdiff.mp hv).1

/-- Equal additions at the leaf and its parent cancel exactly in their bag difference. -/
theorem flap_of_equal_additions (B N R A : Finset V) :
    pullbackBag B R A \ pullbackBag N R A = ((B \ N) ∩ R) \ A := by
  ext v
  simp only [Finset.mem_sdiff,mem_pullbackBag,Finset.mem_inter]
  constructor
  · rintro ⟨hv,hn⟩
    have ha : v ∉ A := fun ha => hn (Or.inr ha)
    obtain ⟨hb,hr⟩ := hv.resolve_right ha
    exact ⟨⟨⟨hb,fun h => hn (Or.inl ⟨h,hr⟩)⟩,hr⟩,ha⟩
  · rintro ⟨⟨⟨hb,hn⟩,hr⟩,ha⟩
    refine ⟨Or.inl ⟨hb,hr⟩,?_⟩
    rintro (h | h)
    · exact hn h.1
    · exact ha h

/-- The local charging condition simultaneously preserves every bag-size bound. -/
theorem all_bag_bounds {T : Type} (bags : T → Finset V) (R : Finset V)
    (added : T → Finset V) (charge : T → V → V) (b : ℕ)
    (hside : ∀ t, added t ⊆ R)
    (hcharge : ∀ t v, v ∈ added t \ bags t → charge t v ∈ bags t \ R)
    (hinj : ∀ t, Set.InjOn (charge t) (added t \ bags t : Finset V))
    (hbound : ∀ t, (bags t).card ≤ b) :
    ∀ t, (pullbackBag (bags t) R (added t)).card ≤ b := by
  intro t
  exact (card_pullbackBag_le (hside t) (charge t) (hcharge t) (hinj t)).trans (hbound t)

end StableMSR.Recovery.BagPullback
open RobertsonSeymour1986.GM5
namespace StableMSR.Recovery.PartialDecompositions
variable {V T : Type} [Fintype V] [DecidableEq V] [DecidableEq T]
/-- Restrict bags to R and route each separator vertex from its occurrence to the root. -/
lemma routedBag_subset {tree : SimpleGraph T} {bags : T → Finset V}
    {R S : Finset V} {root : T} {anchor : V → T}
    {route : ∀ v, tree.Walk root (anchor v)} (hSR : S ⊆ R) (t : T) :
    routedBag tree bags R S root anchor route t ⊆ R := by
  intro v hv
  rcases mem_routedBag.mp hv with h | h
  · exact h.2
  · exact hSR h.1
lemma routedBag_root {tree : SimpleGraph T} {bags : T → Finset V}
    {R S : Finset V} {root : T} {anchor : V → T}
    {route : ∀ v, tree.Walk root (anchor v)}
    (hroot : bags root ∩ R ⊆ S) : routedBag tree bags R S root anchor route root = S := by
  ext v
  constructor
  · intro hv
    rcases mem_routedBag.mp hv with h | h
    · exact hroot (Finset.mem_inter.mpr h)
    · exact h.1
  · intro hv
    exact mem_routedBag.mpr (.inr ⟨hv,(route v).start_mem_support⟩)
/-- Routing preserves the connected occurrence set of every retained vertex. -/
theorem routedBag_running_intersection {G : SimpleGraph V} {tree : SimpleGraph T}
    {bags : T → Finset V} (htd : IsTreeDecomposition G tree bags)
    (R S : Finset V) (hSR : S ⊆ R) (root : T) (anchor : V → T)
    (ha : ∀ v ∈ S, v ∈ bags (anchor v)) (route : ∀ v, tree.Walk root (anchor v)) :
    ∀ (s t u : T) (p : tree.Walk s u), p.IsPath → t ∈ p.support →
      routedBag tree bags R S root anchor route s ∩
      routedBag tree bags R S root anchor route u ⊆
      routedBag tree bags R S root anchor route t := by
  intro s t u p hp ht v hv
  obtain ⟨hvs,hvu⟩ := Finset.mem_inter.mp hv
  by_cases hvS : v ∈ S
  · have toAnchor : ∀ z, v ∈ routedBag tree bags R S root anchor route z →
        ∃ q : tree.Walk z (anchor v), ∀ a ∈ q.support,
          v ∈ routedBag tree bags R S root anchor route a := by
      intro z hz
      rcases mem_routedBag.mp hz with hz | hz
      · obtain ⟨q,hq⟩ := htd.1.connected.exists_isPath z (anchor v)
        refine ⟨q,?_⟩
        intro a ha'
        exact mem_routedBag.mpr (.inl ⟨htd.2.2.2 z a (anchor v) q hq ha'
          (Finset.mem_inter.mpr ⟨hz.1,ha v hvS⟩),hz.2⟩)
      · refine ⟨(route v).dropUntil z hz.2,?_⟩
        intro a ha'
        exact mem_routedBag.mpr (.inr ⟨hvS,(route v).support_dropUntil_subset_support hz.2 ha'⟩)
    obtain ⟨q,hq⟩ := toAnchor s hvs
    obtain ⟨r,hr⟩ := toAnchor u hvu
    let walk := q.append r.reverse
    have he : (⟨p,hp⟩ : tree.Path s u) = walk.toPath :=
      htd.1.isAcyclic.subsingleton_path s u |>.elim _ _
    have hwalk : t ∈ walk.support := by
      have hv := walk.support_toPath_subset_support
      apply hv
      simpa only [← congrArg Subtype.val he] using ht
    rcases (SimpleGraph.Walk.mem_support_append_iff q r.reverse).mp hwalk with h | h
    · exact hq t h
    · exact hr t (by simpa using h)
  · have hs := (mem_routedBag.mp hvs).resolve_right (fun h => hvS h.1)
    have hu := (mem_routedBag.mp hvu).resolve_right (fun h => hvS h.1)
    exact mem_routedBag.mpr (.inl ⟨htd.2.2.2 s t u p hp ht (Finset.mem_inter.mpr ⟨hs.1,hu.1⟩),hs.2⟩)
/-- The restricted bags cover every retained vertex and every edge of the induced side. -/
theorem routedBag_cover {G : SimpleGraph V} {tree : SimpleGraph T}
    {bags : T → Finset V} (htd : IsTreeDecomposition G tree bags)
    (R S : Finset V) (root : T) (anchor : V → T)
    (route : ∀ v, tree.Walk root (anchor v)) :
    (∀ v ∈ R, ∃ t, v ∈ routedBag tree bags R S root anchor route t) ∧
    (∀ x ∈ R, ∀ y ∈ R, G.Adj x y → ∃ t,
      x ∈ routedBag tree bags R S root anchor route t ∧
      y ∈ routedBag tree bags R S root anchor route t) := by
  constructor
  · intro v hv
    obtain ⟨t,ht⟩ := htd.2.1 v
    exact ⟨t,mem_routedBag.mpr (.inl ⟨ht,hv⟩)⟩
  · intro x hx y hy hxy
    obtain ⟨t,htx,hty⟩ := htd.2.2.1 x y hxy
    exact ⟨t,mem_routedBag.mpr (.inl ⟨htx,hx⟩),mem_routedBag.mpr (.inl ⟨hty,hy⟩)⟩
/-- Nonroot leaves acquire no new vertices when the routes are simple paths. -/
theorem routedBag_leaf_eq {G : SimpleGraph V} {tree : SimpleGraph T}
    {bags : T → Finset V} (R S : Finset V) (hSR : S ⊆ R)
    (root : T) (anchor : V → T) (ha : ∀ v ∈ S, v ∈ bags (anchor v))
    (route : ∀ v, tree.Walk root (anchor v)) (hp : ∀ v, (route v).IsPath)
    {t u : T} (htr : t ≠ root) (hleaf : ∀ z, tree.Adj t z → z = u) :
    routedBag tree bags R S root anchor route t = bags t ∩ R := by
  ext v
  constructor
  · intro hv
    rcases mem_routedBag.mp hv with h | h
    · exact Finset.mem_inter.mpr h
    · have ht : t = anchor v :=
        (leaf_mem_path_endpoints hleaf (route v) (hp v) h.2).resolve_left htr
      exact Finset.mem_inter.mpr ⟨ht ▸ ha v h.1,hSR h.1⟩
  · intro hv
    exact mem_routedBag.mpr (.inl (Finset.mem_inter.mp hv))
/-- Every nonroot leaf flap in the restricted tree is contained in its original flap. -/
theorem routedBag_leaf_flap_subset {G : SimpleGraph V} {tree : SimpleGraph T}
    {bags : T → Finset V} (R S : Finset V) (hSR : S ⊆ R)
    (root : T) (anchor : V → T) (ha : ∀ v ∈ S, v ∈ bags (anchor v))
    (route : ∀ v, tree.Walk root (anchor v)) (hp : ∀ v, (route v).IsPath)
    {t u : T} (htr : t ≠ root) (hleaf : ∀ z, tree.Adj t z → z = u) :
    routedBag tree bags R S root anchor route t \
      routedBag tree bags R S root anchor route u ⊆ bags t \ bags u := by
  rw [routedBag_leaf_eq (G := G) R S hSR root anchor ha route hp htr hleaf]
  intro v hv
  obtain ⟨hvt,hvu⟩ := Finset.mem_sdiff.mp hv
  obtain ⟨ht,hR⟩ := Finset.mem_inter.mp hvt
  exact Finset.mem_sdiff.mpr ⟨ht,fun hu => hvu (mem_routedBag.mpr (.inl ⟨hu,hR⟩))⟩
/-- The routed bags give a genuine tree decomposition of the induced retained side. -/
theorem routedBag_induced_decomposition {G : SimpleGraph V} {tree : SimpleGraph T}
    {bags : T → Finset V} (htd : IsTreeDecomposition G tree bags)
    (R S : Finset V) (hSR : S ⊆ R) (root : T) (anchor : V → T)
    (ha : ∀ v ∈ S, v ∈ bags (anchor v)) (route : ∀ v, tree.Walk root (anchor v)) :
    IsTreeDecomposition (G.induce (R : Set V)) tree
      (fun t => (routedBag tree bags R S root anchor route t).subtype (· ∈ R)) := by
  classical
  obtain ⟨hvertex,hedge⟩ := routedBag_cover htd R S root anchor route
  refine ⟨htd.1,?_,?_,?_⟩
  · intro v
    obtain ⟨t,ht⟩ := hvertex v.val v.property
    exact ⟨t,Finset.mem_subtype.mpr ht⟩
  · intro x y hxy
    obtain ⟨t,hx,hy⟩ := hedge x.val x.property y.val y.property hxy
    exact ⟨t,Finset.mem_subtype.mpr hx,Finset.mem_subtype.mpr hy⟩
  · intro s t u p hp ht v hv
    obtain ⟨hs,hu⟩ := Finset.mem_inter.mp hv
    exact Finset.mem_subtype.mpr (routedBag_running_intersection htd R S hSR root anchor ha route
      s t u p hp ht (Finset.mem_inter.mpr ⟨Finset.mem_subtype.mp hs,Finset.mem_subtype.mp hu⟩))
/-- A numerical charging inequality is sufficient; a path linkage need not be supplied. -/
theorem routedBag_card_le {tree : SimpleGraph T} {bags : T → Finset V}
    (R S : Finset V) (hSR : S ⊆ R) (root : T) (anchor : V → T)
    (route : ∀ v, tree.Walk root (anchor v)) (t : T)
    (hcharge : ((S.filter (fun v => t ∈ (route v).support)) \ bags t).card ≤
      (bags t \ R).card) :
    (routedBag tree bags R S root anchor route t).card ≤ (bags t).card := by
  classical
  have hside : S.filter (fun v => t ∈ (route v).support) ⊆ R :=
    fun v hv => hSR (Finset.mem_filter.mp hv).1
  change (BagPullback.pullbackBag (bags t) R _).card ≤ _
  rw [BagPullback.pullbackBag_eq_new_union hside]
  have hu := Finset.card_union_le (bags t ∩ R) (S.filter (fun v => t ∈ (route v).support) \ bags t)
  have hb := Finset.card_inter_add_card_sdiff (bags t) R
  omega
end StableMSR.Recovery.PartialDecompositions
open RobertsonSeymour1986.GM5
namespace StableMSR.Recovery.PartialDecompositions
variable {V T : Type} [Fintype V] [DecidableEq V] [DecidableEq T]
/-- Side restriction with separator routing preserves partial decompositions whenever
new vertices can be charged numerically to vertices removed from each bag. -/
theorem routed_partial {G : SimpleGraph V} {tree : SimpleGraph T}
    {bags : T → Finset V} {b : ℕ} (h : IsPartial G b tree bags)
    (R S : Finset V) (hSR : S ⊆ R) (hSb : S.card ≤ b)
    (root : T) (hroot : bags root ∩ R ⊆ S) (anchor : V → T)
    (ha : ∀ v ∈ S, v ∈ bags (anchor v)) (route : ∀ v, tree.Walk root (anchor v))
    (hcharge : ∀ t, ((S.filter (fun v => t ∈ (route v).support)) \ bags t).card ≤
      (bags t \ R).card) :
    IsPartial (G.induce (R : Set V)) b tree
      (fun t => (routedBag tree bags R S root anchor route t).subtype (· ∈ R)) := by
  classical
  have hcard : ∀ t, ((routedBag tree bags R S root anchor route t).subtype (· ∈ R)).card ≤ (bags t).card := by
    intro t
    rw [Finset.card_subtype]
    exact (Finset.card_filter_le _ _).trans (routedBag_card_le R S hSR root anchor route t (hcharge t))
  refine ⟨routedBag_induced_decomposition h.1 R S hSR root anchor ha route,?_,?_⟩
  · refine ⟨root,?_⟩
    change ((routedBag tree bags R S root anchor route root).subtype (· ∈ R)).card ≤ b
    rw [routedBag_root (route := route) hroot,Finset.card_subtype]
    exact (Finset.card_filter_le _ _).trans hSb
  · intro t ht
    obtain ⟨u,htu,hu,hunique⟩ := h.2.2 t (lt_of_lt_of_le ht (hcard t))
    exact ⟨u,htu,(hcard u).trans hu,hunique⟩
/-- The modified half eliminates the selected root flap and only shrinks other flaps. -/
theorem routed_flaps_refine {G : SimpleGraph V} {tree : SimpleGraph T}
    {bags : T → Finset V} {b : ℕ} (h : IsPartial G b tree bags)
    (R S : Finset V) (hSR : S ⊆ R) (hSb : S.card ≤ b)
    (root u : T) (hroot : bags root ∩ R ⊆ S)
    (hrootleaf : ∀ z, tree.Adj root z → z = u)
    (anchor : V → T) (ha : ∀ v ∈ S, v ∈ bags (anchor v))
    (route : ∀ v, tree.Walk root (anchor v)) (hp : ∀ v, (route v).IsPath)
    (hcharge : ∀ t, ((S.filter (fun v => t ∈ (route v).support)) \ bags t).card ≤
      (bags t \ R).card) :
    ∀ C ∈ flaps b tree (routedBag tree bags R S root anchor route),
      ∃ A ∈ flaps b tree bags, A ≠ bags root \ bags u ∧ C ⊆ A := by
  intro C hC
  obtain ⟨t,v,hbig,htv,rfl⟩ := mem_flaps.mp hC
  have htr : t ≠ root := by
    intro heq; subst t
    rw [routedBag_root hroot] at hbig
    omega
  have htbig : b < (bags t).card := lt_of_lt_of_le hbig
    (routedBag_card_le R S hSR root anchor route t (hcharge t))
  obtain ⟨v',htv',hv',huniq⟩ := h.2.2 t htbig
  have hvv := huniq v htv
  subst v'
  have hA : bags t \ bags v ∈ flaps b tree bags := mem_flaps.mpr ⟨t,v,htbig,htv,rfl⟩
  refine ⟨bags t \ bags v,hA,?_,routedBag_leaf_flap_subset (G := G) R S hSR root anchor ha route hp htr huniq⟩
  intro heq
  obtain ⟨x,hx⟩ := flap_nonempty h hA
  have hxroot : x ∈ bags root \ bags u := heq ▸ hx
  exact htr (leaf_exclusive_only h.1 hrootleaf hxroot (Finset.mem_sdiff.mp hx).1)
end StableMSR.Recovery.PartialDecompositions
open RobertsonSeymour1986.GM5
namespace StableMSR.Recovery.PartialDecompositions.SeparatorCharging
lemma lift_connected_walk {V T : Type} [DecidableEq V] [DecidableEq T]
    (G : SimpleGraph V) (tree : SimpleGraph T) (bags : T → Finset V)
    (htd : IsTreeDecomposition G tree bags) {C : Finset V} {u v : V}
    (p : G.Walk u v) (hp : ∀ z ∈ p.support, z ∈ C)
    (s t : T) (hs : u ∈ bags s) (ht : v ∈ bags t) :
    ∃ q : tree.Walk s t, ∀ z ∈ q.support, ∃ c ∈ C, c ∈ bags z := by
  induction p generalizing s with
  | nil =>
    obtain ⟨q,hq⟩ := htd.1.connected.exists_isPath s t
    refine ⟨q,?_⟩
    intro z hz
    exact ⟨_, hp _ (by simp), htd.2.2.2 s z t q hq hz (Finset.mem_inter.mpr ⟨hs,ht⟩)⟩
  | @cons u v w huv p ih =>
    obtain ⟨b,hbu,hbv⟩ := htd.2.2.1 u v huv
    obtain ⟨q,hq⟩ := htd.1.connected.exists_isPath s b
    have htail : ∀ z ∈ p.support, z ∈ C := by
      intro z hz; exact hp z (by simp only [SimpleGraph.Walk.support_cons,List.mem_cons]; exact Or.inr hz)
    obtain ⟨r,hr⟩ := ih htail b hbv ht
    refine ⟨q.append r,?_⟩
    intro z hz
    have hz' : z ∈ q.support ∨ z ∈ r.support := by
      exact (SimpleGraph.Walk.mem_support_append_iff q r).mp hz
    rcases hz' with hzq | hzr
    · exact ⟨u,hp u (by simp),htd.2.2.2 s z b q hq hzq (Finset.mem_inter.mpr ⟨hs,hbu⟩)⟩
    · exact hr z hzr

/-- A graph walk whose endpoint bags straddle a tree node meets that node's bag. -/
theorem walk_hits_intermediate_bag {V T : Type} [DecidableEq V] [DecidableEq T]
    {G : SimpleGraph V} {tree : SimpleGraph T} {bags : T → Finset V}
    (htd : IsTreeDecomposition G tree bags) {u v : V} {root anchor t : T}
    (hu : u ∈ bags root) (hv : v ∈ bags anchor)
    (route : tree.Walk root anchor) (hr : route.IsPath) (ht : t ∈ route.support)
    (p : G.Walk u v) : ∃ z ∈ p.support, z ∈ bags t := by
  classical
  obtain ⟨q,hq⟩ := lift_connected_walk G tree bags htd p
    (C := p.support.toFinset) (fun z hz => List.mem_toFinset.mpr hz) root anchor hu hv
  have he : (⟨route,hr⟩ : tree.Path root anchor) = q.toPath :=
    htd.1.isAcyclic.subsingleton_path root anchor |>.elim _ _
  have htq : t ∈ q.support := by
    apply q.support_toPath_subset_support
    simpa only [← congrArg Subtype.val he] using ht
  obtain ⟨z,hz,hzt⟩ := hq t htq
  exact ⟨z,List.mem_toFinset.mp hz,hzt⟩
/-- A newly routed separator vertex forces every graph walk to its occurrence
through an old bag vertex; if all other walk vertices are outside the retained
side, this gives a deleted vertex to charge against. -/
theorem walk_hits_removed_vertex {V T : Type} [DecidableEq V] [DecidableEq T]
    {G : SimpleGraph V} {tree : SimpleGraph T} {bags : T → Finset V}
    (htd : IsTreeDecomposition G tree bags) {B : Finset V} {u s : V} {root anchor t : T}
    (hu : u ∈ bags root) (hs : s ∈ bags anchor) (hsnot : s ∉ bags t)
    (route : tree.Walk root anchor) (hr : route.IsPath) (ht : t ∈ route.support)
    (p : G.Walk u s) (hp : ∀ z ∈ p.support, z ≠ s → z ∉ B) :
    ∃ z ∈ p.support, z ∈ bags t \ B := by
  obtain ⟨z,hzp,hzt⟩ := walk_hits_intermediate_bag htd hu hs route hr ht p
  refine ⟨z,hzp,Finset.mem_sdiff.mpr ⟨hzt,hp z hzp ?_⟩⟩
  intro he
  subst z
  exact hsnot hzt
/-- First entry into a side of a separation, with a prefix that is exterior
except for its last vertex. -/
lemma first_entry_prefix {V : Type} [DecidableEq V] {G : SimpleGraph V}
    {B S : Finset V}
    (hboundary : ∀ x, x ∉ B → ∀ y, G.Adj x y → y ∈ B → y ∈ S)
    {u v : V} (p : G.Walk u v) (hu : u ∉ B) (hv : v ∈ B) :
    ∃ s ∈ S, ∃ q : G.Walk u s,
      (∀ z ∈ q.support, z ∈ p.support) ∧
      (∀ z ∈ q.support, z ≠ s → z ∉ B) := by
  induction p with
  | nil => exact False.elim (hu hv)
  | @cons u x v hux p ih =>
    by_cases hx : x ∈ B
    · refine ⟨x,hboundary u hu x hux hx,.cons hux .nil,?_,?_⟩
      · intro z hz
        simp only [SimpleGraph.Walk.support_cons,SimpleGraph.Walk.support_nil,List.mem_cons,List.not_mem_nil,or_false] at hz
        rcases hz with rfl | rfl <;> simp
      · intro z hz hne
        simp only [SimpleGraph.Walk.support_cons,SimpleGraph.Walk.support_nil,List.mem_cons,List.not_mem_nil,or_false] at hz
        rcases hz with rfl | rfl
        · exact hu
        · exact False.elim (hne rfl)
    · obtain ⟨s,hs,q,hq,hout⟩ := ih hx hv
      refine ⟨s,hs,.cons hux q,?_,?_⟩
      · intro z hz
        simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at hz ⊢
        exact hz.elim Or.inl (fun h => Or.inr (hq z h))
      · intro z hz hne
        simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact hu
        · exact hout z hz hne

/-- Replacing the separator vertices routed through t by the old vertices
removed from its bag still separates the root bag from the retained side. -/
theorem replacement_separator {V T : Type} [DecidableEq V] [DecidableEq T]
    {G : SimpleGraph V} {tree : SimpleGraph T} {bags : T → Finset V}
    (htd : IsTreeDecomposition G tree bags) {B S Q : Finset V} {root t : T}
    (anchor : V → T) (route : ∀ s, tree.Walk root (anchor s))
    (hr : ∀ s ∈ S, (route s).IsPath) (ha : ∀ s ∈ S, s ∈ bags (anchor s))
    (hQ : ∀ s ∈ Q, s ∈ S ∧ s ∉ bags t ∧ t ∈ (route s).support)
    (hroot : bags root ∩ B ⊆ S)
    (hboundary : ∀ x, x ∉ B → ∀ y, G.Adj x y → y ∈ B → y ∈ S)
    {u v : V} (hu : u ∈ bags root) (hv : v ∈ B) (p : G.Walk u v) :
    ∃ z ∈ p.support, z ∈ (S \ Q) ∪ (bags t \ B) := by
  classical
  by_contra hno
  have havoid : ∀ z ∈ p.support, z ∉ (S \ Q) ∪ (bags t \ B) := by
    intro z hz hin
    exact hno ⟨z,hz,hin⟩
  have huB : u ∉ B := by
    intro huB
    have huS := hroot (Finset.mem_inter.mpr ⟨hu,huB⟩)
    have huQ : u ∈ Q := by
      by_contra hn
      exact havoid u p.start_mem_support (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨huS,hn⟩))
    obtain ⟨_,hun,htu⟩ := hQ u huQ
    exact hun (htd.2.2.2 root t (anchor u) (route u) (hr u huS) htu
      (Finset.mem_inter.mpr ⟨hu,ha u huS⟩))
  obtain ⟨s,hs,q,hqp,hout⟩ := first_entry_prefix hboundary p huB hv
  have hsQ : s ∈ Q := by
    by_contra hn
    exact havoid s (hqp s q.end_mem_support)
      (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hs,hn⟩))
  obtain ⟨_,hsn,hts⟩ := hQ s hsQ
  obtain ⟨z,hz,hzm⟩ := walk_hits_removed_vertex htd hu (ha s hs) hsn
    (route s) (hr s hs) hts q hout
  exact havoid z (hqp z hz) (Finset.mem_union_right _ hzm)
/-- Minimum separator size pays for every genuinely added separator vertex. -/
theorem replacement_card_le {V T : Type} [DecidableEq V] [DecidableEq T]
    {G : SimpleGraph V} {tree : SimpleGraph T} {bags : T → Finset V}
    (htd : IsTreeDecomposition G tree bags) {B S Q target : Finset V} {root t : T}
    (anchor : V → T) (route : ∀ s, tree.Walk root (anchor s))
    (hr : ∀ s ∈ S, (route s).IsPath) (ha : ∀ s ∈ S, s ∈ bags (anchor s))
    (hQ : ∀ s ∈ Q, s ∈ S ∧ s ∉ bags t ∧ t ∈ (route s).support)
    (hroot : bags root ∩ B ⊆ S) (hSB : S ⊆ B) (htarget : target ⊆ B)
    (hboundary : ∀ x, x ∉ B → ∀ y, G.Adj x y → y ∈ B → y ∈ S)
    (hmin : ∀ D : Finset V,
      (∀ u ∈ bags root, ∀ v ∈ target, ∀ p : G.Walk u v, ∃ z ∈ p.support, z ∈ D) →
      S.card ≤ D.card) : Q.card ≤ (bags t \ B).card := by
  have hsep := hmin ((S \ Q) ∪ (bags t \ B)) (fun u hu v hv p =>
    replacement_separator htd anchor route hr ha hQ hroot hboundary hu (htarget hv) p)
  have hdis : Disjoint (S \ Q) (bags t \ B) := by
    apply Finset.disjoint_left.mpr
    intro v hvS hvM
    exact (Finset.mem_sdiff.mp hvM).2 (hSB (Finset.mem_sdiff.mp hvS).1)
  rw [Finset.card_union_of_disjoint hdis, Finset.card_sdiff_of_subset (fun s hs => (hQ s hs).1)] at hsep
  have hle := Finset.card_le_card (show Q ⊆ S from fun s hs => (hQ s hs).1)
  omega
/-- The bag-size bound for separator routing, proved from separator minimality
rather than from a disjoint-paths theorem. -/
theorem routedBag_card_le_of_minimum_separator
    {V T : Type} [Fintype V] [DecidableEq V] [DecidableEq T]
    {G : SimpleGraph V} {tree : SimpleGraph T} {bags : T → Finset V}
    (htd : IsTreeDecomposition G tree bags) {B S target : Finset V} {root : T}
    (anchor : V → T) (route : ∀ s, tree.Walk root (anchor s))
    (hr : ∀ s ∈ S, (route s).IsPath) (ha : ∀ s ∈ S, s ∈ bags (anchor s))
    (hroot : bags root ∩ B ⊆ S) (hSB : S ⊆ B) (htarget : target ⊆ B)
    (hboundary : ∀ x, x ∉ B → ∀ y, G.Adj x y → y ∈ B → y ∈ S)
    (hmin : ∀ D : Finset V,
      (∀ u ∈ bags root, ∀ v ∈ target, ∀ p : G.Walk u v, ∃ z ∈ p.support, z ∈ D) →
      S.card ≤ D.card) (t : T) :
    (routedBag tree bags B S root anchor route t).card ≤ (bags t).card := by
  classical
  let R := S.filter (fun s => t ∈ (route s).support)
  let Q := R \ bags t
  have hQ : ∀ s ∈ Q, s ∈ S ∧ s ∉ bags t ∧ t ∈ (route s).support := by
    intro s hs
    obtain ⟨hsR,hsnot⟩ := Finset.mem_sdiff.mp hs
    obtain ⟨hsS,hsroute⟩ := Finset.mem_filter.mp hsR
    exact ⟨hsS,hsnot,hsroute⟩
  have hc := replacement_card_le htd anchor route hr ha hQ hroot hSB htarget hboundary hmin
  have heq : routedBag tree bags B S root anchor route t = (bags t ∩ B) ∪ Q := by
    ext v
    simp only [mem_routedBag,Finset.mem_union,Finset.mem_inter,Q,Finset.mem_sdiff]
    constructor
    · rintro (hv | ⟨hvS,hvr⟩)
      · exact Or.inl hv
      · by_cases hvbag : v ∈ bags t
        · exact Or.inl ⟨hvbag,hSB hvS⟩
        · exact Or.inr ⟨Finset.mem_filter.mpr ⟨hvS,hvr⟩,hvbag⟩
    · rintro (hv | ⟨hvR,hvn⟩)
      · exact Or.inl hv
      · exact Or.inr (Finset.mem_filter.mp hvR)
  rw [heq]
  calc
    ((bags t ∩ B) ∪ Q).card ≤ (bags t ∩ B).card + Q.card := Finset.card_union_le _ _
    _ ≤ (bags t ∩ B).card + (bags t \ B).card := Nat.add_le_add_left hc _
    _ = (bags t).card := Finset.card_inter_add_card_sdiff _ _
end StableMSR.Recovery.PartialDecompositions.SeparatorCharging
open RobertsonSeymour1986.GM5

/-- One whole side of the gluing construction, including cardinality and flap control. -/
theorem solution {V T : Type} [Fintype V] [DecidableEq V] [DecidableEq T]
    {G : SimpleGraph V} {tree : SimpleGraph T} {bags : T → Finset V} {b : ℕ}
    (h : IsPartial G b tree bags) (B S target : Finset V) (root u : T)
    (hSb : S.card ≤ b) (hSB : S ⊆ B) (htarget : target ⊆ B)
    (hroot : bags root ∩ B ⊆ S) (hleaf : ∀ z, tree.Adj root z → z = u)
    (hboundary : ∀ x, x ∉ B → ∀ y, G.Adj x y → y ∈ B → y ∈ S)
    (hmin : ∀ D : Finset V,
      (∀ x ∈ bags root, ∀ y ∈ target, ∀ p : G.Walk x y, ∃ z ∈ p.support, z ∈ D) →
      S.card ≤ D.card) :
    ∃ newbags : T → Finset V,
      newbags root = S ∧ (∀ t, newbags t ⊆ B) ∧
      (∀ t, (newbags t).card ≤ (bags t).card) ∧
      IsPartial (G.induce (B : Set V)) b tree (fun t => (newbags t).subtype (· ∈ B)) ∧
      ∀ C ∈ flaps b tree newbags,
        ∃ A ∈ flaps b tree bags, A ≠ bags root \ bags u ∧ C ⊆ A := by
  classical
  choose anchor ha using h.1.2.1
  have hex : ∀ v : V, ∃ p : tree.Walk root (anchor v), p.IsPath :=
    fun v => h.1.1.connected.exists_isPath root (anchor v)
  choose route hp using hex
  have haS : ∀ v ∈ S, v ∈ bags (anchor v) := fun v _ => ha v
  have hcharge : ∀ t, (S.filter (fun v => t ∈ (route v).support) \ bags t).card ≤
      (bags t \ B).card := by
    intro t
    apply SeparatorCharging.replacement_card_le h.1 anchor route (fun v _ => hp v) haS
      (B := B) (S := S) (target := target)
    · intro v hv
      obtain ⟨hvf,hvn⟩ := Finset.mem_sdiff.mp hv
      obtain ⟨hvs,hvp⟩ := Finset.mem_filter.mp hvf
      exact ⟨hvs,hvn,hvp⟩
    · exact hroot
    · exact hSB
    · exact htarget
    · exact hboundary
    · exact hmin
  refine ⟨routedBag tree bags B S root anchor route,routedBag_root hroot,
    routedBag_subset hSB,?_,?_,?_⟩
  · exact fun t => routedBag_card_le B S hSB root anchor route t (hcharge t)
  · exact routed_partial h B S hSB hSb root hroot anchor haS route hcharge
  · exact routed_flaps_refine h B S hSB hSb root u hroot hleaf anchor haS route hp hcharge

