-- Prove2me | solution 1 for NonCutPoints.exists_two_noncut_points
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:33:52.098+00:00
-- url     : https://prove2.me/submissions/3523ad39-8832-44a1-a95c-119f2e6c8390

module
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Order.Zorn
public import Definitions.Def_NonCutPoints_Solution
section
@[expose] public section
open Set
universe u
namespace NonCutPoints
variable {X : Type u} [tX : TopologicalSpace X]
private theorem Cutting.not_left {x : X} (d : Cutting x) : x ∉ d.left := by
  intro hx
  have hmem : x ∈ d.left ∪ d.right := Or.inl hx
  rw [d.cover] at hmem
  simp at hmem
private theorem Cutting.not_right {x : X} (d : Cutting x) : x ∉ d.right := by
  intro hx
  have hmem : x ∈ d.left ∪ d.right := Or.inr hx
  rw [d.cover] at hmem
  simp at hmem
private theorem Cutting.insert_eq_compl {x : X} (d : Cutting x) :
    insert x d.left = d.rightᶜ := by
  ext z
  have h := congrArg (fun s : Set X => z ∈ s) d.cover
  simp only [mem_union, mem_compl_iff, mem_singleton_iff] at h
  have hd := disjoint_left.1 d.disjoint
  simp only [mem_insert_iff, mem_compl_iff]
  by_cases hz : z = x
  · subst z
    simp [d.not_right]
  · constructor
    · rintro (heq | hl)
      · exact (hz heq).elim
      · exact fun hr => hd hl hr
    · intro hr
      exact Or.inr ((h.mpr hz).resolve_right hr)
private theorem Cutting.subset_side {x : X} (d : Cutting x) {S : Set X}
    (hS : IsPreconnected S) (hx : x ∉ S) : S ⊆ d.left ∨ S ⊆ d.right := by
  apply hS.subset_or_subset d.left_open d.right_open d.disjoint
  intro z hz
  rw [d.cover]
  simpa only [mem_compl_iff, mem_singleton_iff] using
    (show z ≠ x from fun heq => hx (heq ▸ hz))
private theorem Cutting.connected_insert [PreconnectedSpace X] {x : X} (d : Cutting x) :
    IsConnected (insert x d.left) := by
  refine ⟨⟨x, mem_insert x _⟩, ?_⟩
  have hclosed : IsClosed (insert x d.left) := by
    rw [d.insert_eq_compl]
    exact d.right_open.isClosed_compl
  apply (isPreconnected_iff_subset_of_fully_disjoint_closed hclosed).2
  intro a b ha hb hcover hab
  have hcase : ∀ (a b : Set X), IsClosed a → IsClosed b →
      insert x d.left ⊆ a ∪ b → Disjoint a b → x ∈ a → insert x d.left ⊆ a := by
    intro a b ha hb hc hd hxa
    have hxb : x ∉ b := fun hxb => disjoint_left.1 hd hxa hxb
    have heq : (insert x d.left) ∩ b = d.left ∩ aᶜ := by
      ext z
      constructor
      · rintro ⟨hz, hzb⟩
        refine ⟨?_, fun hza => disjoint_left.1 hd hza hzb⟩
        exact hz.resolve_left (fun heq => hxb (heq ▸ hzb))
      · rintro ⟨hz, hza⟩
        exact ⟨mem_insert_of_mem _ hz, (hc (mem_insert_of_mem _ hz)).resolve_left hza⟩
    have hclopen : IsClopen ((insert x d.left) ∩ b) :=
      ⟨hclosed.inter hb, heq ▸ d.left_open.inter ha.isOpen_compl⟩
    have hempty : (insert x d.left) ∩ b = ∅ := by
      rcases isClopen_iff.mp hclopen with hempty | huniv
      · exact hempty
      · have : x ∈ (insert x d.left) ∩ b := huniv ▸ mem_univ x
        exact (hxb this.2).elim
    intro z hz
    exact (hc hz).resolve_right (fun hzb => by
      have : z ∈ (insert x d.left) ∩ b := ⟨hz, hzb⟩
      simp [hempty] at this)
  rcases hcover (mem_insert x d.left) with hxa | hxb
  · exact Or.inl (hcase a b ha hb hcover hab hxa)
  · exact Or.inr (hcase b a hb ha (by simpa [union_comm] using hcover) hab.symm hxb)
private theorem exists_cutting [T1Space X] {x : X}
    (hne : ({x}ᶜ : Set X).Nonempty) (hcut : ¬ IsConnected ({x}ᶜ : Set X)) :
    Nonempty (Cutting x) := by
  have hp : ¬ IsPreconnected ({x}ᶜ : Set X) := fun h => hcut ⟨hne, h⟩
  simp only [IsPreconnected, not_forall] at hp
  obtain ⟨a, b, ha, hb, hcover, hna, hnb, hdisj⟩ := hp
  refine ⟨⟨{x}ᶜ ∩ a, {x}ᶜ ∩ b, isOpen_compl_singleton.inter ha,
    isOpen_compl_singleton.inter hb, hna, hnb, ?_, ?_⟩⟩
  · apply disjoint_left.2
    rintro z ⟨hz, hza⟩ ⟨_, hzb⟩
    exact hdisj ⟨z, hz, hza, hzb⟩
  · ext z
    constructor
    · rintro (⟨hz, _⟩ | ⟨hz, _⟩) <;> exact hz
    · intro hz
      rcases hcover hz with hza | hzb
      · exact Or.inl ⟨hz, hza⟩
      · exact Or.inr ⟨hz, hzb⟩
private theorem Cutting.subset_left {x : X} (d : Cutting x) {S : Set X}
    (hS : IsPreconnected S) (hx : x ∉ S) {y : X} (hyS : y ∈ S)
    (hyL : y ∈ d.left) : S ⊆ d.left := by
  rcases d.subset_side hS hx with h | h
  · exact h
  · exact (disjoint_left.1 d.disjoint hyL (h hyS)).elim
private theorem exists_oriented_cutting [T1Space X] [PreconnectedSpace X]
    {c x : X} (d : Cutting c) (hx : x ∈ d.left)
    (hcut : ¬ IsConnected ({x}ᶜ : Set X)) :
    ∃ e : Cutting x, e.left ⊆ d.left ∧ c ∈ e.right := by
  have hcx : c ≠ x := fun heq => d.not_left (heq ▸ hx)
  obtain ⟨e⟩ := exists_cutting ⟨c, by simpa using hcx⟩ hcut
  have hxS : x ∉ insert c d.right := by
    rintro (heq | hr)
    · exact hcx heq.symm
    · exact disjoint_left.1 d.disjoint hx hr
  have orient : ∀ e : Cutting x, insert c d.right ⊆ e.right →
      e.left ⊆ d.left ∧ c ∈ e.right := by
    intro e hS
    refine ⟨?_, hS (mem_insert c _)⟩
    intro z hz
    have hzc : z ≠ c := fun heq =>
      disjoint_left.1 e.disjoint hz (heq ▸ hS (mem_insert c _))
    have hzR : z ∉ d.right := fun hr =>
      disjoint_left.1 e.disjoint hz (hS (mem_insert_of_mem _ hr))
    have hzcover : z ∈ d.left ∪ d.right := by
      rw [d.cover]
      simpa using hzc
    exact hzcover.resolve_right hzR
  rcases e.subset_side d.swap.connected_insert.isPreconnected hxS with h | h
  · exact ⟨e.swap, orient e.swap h⟩
  · exact ⟨e, orient e h⟩
private theorem Cutting.tail_subset [PreconnectedSpace X] {c x y : X}
    (e : Cutting x) (f : Cutting y) (hcE : c ∈ e.right) (hcF : c ∈ f.right)
    (hyE : y ∈ e.left) : insert y f.left ⊆ e.left := by
  have hyx : y ≠ x := fun heq => e.not_left (heq ▸ hyE)
  have hxF : x ∉ f.left := by
    intro hxF
    have hxS : x ∉ insert y f.right := by
      rintro (heq | hr)
      · exact hyx heq.symm
      · exact disjoint_left.1 f.disjoint hxF hr
    have hS : insert y f.right ⊆ e.left :=
      e.subset_left f.swap.connected_insert.isPreconnected hxS (mem_insert y _) hyE
    exact disjoint_left.1 e.disjoint (hS (mem_insert_of_mem _ hcF)) hcE
  have hxS : x ∉ insert y f.left := by
    rintro (heq | hl)
    · exact hyx heq.symm
    · exact hxF hl
  exact e.subset_left f.connected_insert.isPreconnected hxS (mem_insert y _) hyE
private theorem Cutting.exists_noncut_in_left [T2Space X] [CompactSpace X]
    [PreconnectedSpace X] {c : X} (d : Cutting c) :
    ∃ x ∈ d.left, IsConnected ({x}ᶜ : Set X) := by
  classical
  by_contra h
  have hcut : ∀ x ∈ d.left, ¬ IsConnected ({x}ᶜ : Set X) := by
    simpa only [not_exists, not_and] using h
  choose E hEL hcE using fun x : d.left =>
    exists_oriented_cutting d x.2 (hcut x x.2)
  let F : d.left → Set X := fun x => insert (x : X) (E x).left
  have hFU : ∀ x, F x ⊆ d.left := fun x => insert_subset x.2 (hEL x)
  have hcompact : ∀ x, IsCompact (F x) := by
    intro x
    change IsCompact (insert (x : X) (E x).left)
    rw [(E x).insert_eq_compl]
    exact (E x).right_open.isClosed_compl.isCompact
  have hnonempty : ∀ x, (F x).Nonempty := fun x => ⟨x, mem_insert _ _⟩
  have hnest : ∀ i j : d.left, (i : X) ∈ F j → F i ⊆ F j := by
    intro i j hi
    rcases hi with heq | hi
    · have hij : i = j := Subtype.ext heq
      subst i
      exact Subset.rfl
    · exact ((E j).tail_subset (E i) (hcE j) (hcE i) hi).trans (subset_insert _ _)
  have hchain : ∀ s ⊆ range F, IsChain (· ⊆ ·) s → s.Nonempty →
      ∃ lb ∈ range F, ∀ t ∈ s, lb ⊆ t := by
    intro s hs htotal hne
    let : Nonempty s := hne.to_subtype
    let G : s → Set X := fun i => i.1
    have hdir : Directed (fun a b => b ⊆ a) G := by
      intro i j
      rcases htotal.total i.2 j.2 with hij | hji
      · exact ⟨i, Subset.rfl, hij⟩
      · exact ⟨j, hji, Subset.rfl⟩
    have hgc : ∀ i, IsCompact (G i) := by
      intro i
      obtain ⟨x, hx⟩ := hs i.2
      change IsCompact i.val
      rw [← hx]
      exact hcompact x
    have hgn : ∀ i, (G i).Nonempty := by
      intro i
      obtain ⟨x, hx⟩ := hs i.2
      change i.val.Nonempty
      rw [← hx]
      exact hnonempty x
    obtain ⟨m, hm⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      G hdir hgn hgc (fun i => (hgc i).isClosed)
    let i0 : s := Classical.arbitrary s
    obtain ⟨x0, hx0⟩ := hs i0.2
    have hmU : m ∈ d.left := hFU x0 (hx0.symm ▸ mem_iInter.1 hm i0)
    let mU : d.left := ⟨m, hmU⟩
    refine ⟨F mU, mem_range_self mU, ?_⟩
    intro t ht
    obtain ⟨x, hx⟩ := hs ht
    rw [← hx]
    apply hnest mU x
    exact hx.symm ▸ mem_iInter.1 hm ⟨t, ht⟩
  obtain ⟨x0, hx0⟩ := d.left_nonempty
  let p0 : d.left := ⟨x0, hx0⟩
  obtain ⟨K, _, hminimal⟩ :=
    zorn_superset_nonempty (range F) hchain (F p0) (mem_range_self p0)
  obtain ⟨m, rfl⟩ := hminimal.prop
  obtain ⟨r, hr⟩ := (E m).left_nonempty
  let rU : d.left := ⟨r, hEL m hr⟩
  have hsub : F rU ⊆ (E m).left :=
    (E m).tail_subset (E rU) (hcE m) (hcE rU) hr
  have heq : F rU = F m :=
    hminimal.eq_of_subset (mem_range_self rU) (hsub.trans (subset_insert _ _))
  have hm : (m : X) ∈ F rU := heq.symm ▸ mem_insert _ _
  exact (E m).not_left (hsub hm)
private theorem exists_pair_univ [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [Nontrivial X] : ∃ x y : X, x ≠ y ∧ IsConnected ({x}ᶜ : Set X) ∧
      IsConnected ({y}ᶜ : Set X) := by
  classical
  by_cases h : ∀ x : X, IsConnected ({x}ᶜ : Set X)
  · obtain ⟨x, y, hxy⟩ := exists_pair_ne X
    exact ⟨x, y, hxy, h x, h y⟩
  · push Not at h
    obtain ⟨c, hc⟩ := h
    obtain ⟨z, hzc⟩ := exists_ne c
    obtain ⟨d⟩ := exists_cutting ⟨z, by simpa using hzc⟩ hc
    obtain ⟨x, hx, hxc⟩ := d.exists_noncut_in_left
    obtain ⟨y, hy, hyc⟩ := d.swap.exists_noncut_in_left
    refine ⟨x, y, ?_, hxc, hyc⟩
    intro heq
    exact disjoint_left.1 d.disjoint hx (heq.symm ▸ hy)
omit [TopologicalSpace X] in
private theorem image_compl_singleton {C : Set X} (x : C) :
    ((↑) : C → X) '' ({x}ᶜ : Set C) = C \ {(x : X)} := by
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a.2, ?_⟩
    simp only [mem_compl_iff, mem_singleton_iff] at ha
    simpa only [mem_singleton_iff] using
      (show (a : X) ≠ (x : X) from fun heq => ha (Subtype.ext heq))
  · rintro ⟨hz, hzx⟩
    refine ⟨⟨z, hz⟩, ?_, rfl⟩
    simp only [mem_compl_iff, mem_singleton_iff]
    intro heq
    exact hzx (congrArg Subtype.val heq)
end NonCutPoints
end
end

set_option autoImplicit true
@[expose] public section
public section
open Set
universe u
open NonCutPoints
variable {X : Type u} [tX : TopologicalSpace X]
namespace NonCutPoints
theorem _root_.solution [t2X : T2Space X] {C : Set X}
    (hCcompact : IsCompact C) (hCconnected : IsConnected C) (hCnontrivial : C.Nontrivial) :
    ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ IsConnected (C \ {x}) ∧ IsConnected (C \ {y}) := by
  let : CompactSpace C := isCompact_iff_compactSpace.mp hCcompact
  let : ConnectedSpace C := isConnected_iff_connectedSpace.mp hCconnected
  let : Nontrivial C := hCnontrivial.coe_sort
  obtain ⟨x, y, hxy, hx, hy⟩ := exists_pair_univ (X := C)
  refine ⟨x, x.2, y, y.2, fun heq => hxy (Subtype.ext heq), ?_, ?_⟩
  · rw [← image_compl_singleton x]
    exact hx.image _ continuous_subtype_val.continuousOn
  · rw [← image_compl_singleton y]
    exact hy.image _ continuous_subtype_val.continuousOn
end NonCutPoints
