-- Prove2me | solution 1 for ImprovedMMS.Additive.lemma_3_7
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T17:07:37.616598+00:00
-- url     : https://prove2.me/submissions/d262c5b0-f0d3-42d7-95a1-4b1cd9bea20e

import Mathlib
import Definitions.Def_ImprovedMMS_Additive_Bipartite

set_option autoImplicit false
open ImprovedMMS.Additive

theorem ims_l36 {α β : Type*} [DecidableEq α] [DecidableEq β]
    (X : Finset α) (Y : Finset β) (E : Finset (α × β)) (hE : E ⊆ X ×ˢ Y)
    (Mt : Finset (α × β)) (hM : IsMaxMatching E Mt) :
    ∀ T ⊆ X \ FH E Mt X Y, T.Nonempty → T.card < (nbhd E T).card := by
  intro T hT hTne
  obtain ⟨hMsub, hM1, hM2⟩ := hM.1
  -- the set of mates of T
  set MT : Finset β := (Mt.filter (fun e => e.1 ∈ T)).image Prod.snd with hMT
  have hmemMT : ∀ y, y ∈ MT ↔ ∃ x ∈ T, (x, y) ∈ Mt := by
    intro y
    simp only [hMT, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨e, ⟨he, hx⟩, rfl⟩
      exact ⟨e.1, hx, he⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨(x, y), ⟨hxy, hx⟩, rfl⟩
  -- every vertex of T is matched to a reachable vertex
  have hmatched : ∀ x ∈ T, ∃ y, AltReach E Mt Y y ∧ (x, y) ∈ Mt := by
    intro x hx
    have := hT hx
    rw [Finset.mem_sdiff] at this
    obtain ⟨hxX, hxF⟩ := this
    classical
    simp only [FH, Finset.mem_filter] at hxF
    by_contra hcon
    exact hxF ⟨hxX, hcon⟩
  -- |MT| = |T|
  have hcard : MT.card = T.card := by
    have h1 : (Mt.filter (fun e => e.1 ∈ T)).card = T.card := by
      refine Finset.card_bij (fun e _ => e.1) ?_ ?_ ?_
      · intro e he
        exact (Finset.mem_filter.mp he).2
      · intro e he e' he' h
        exact hM1 e (Finset.mem_filter.mp he).1 e' (Finset.mem_filter.mp he').1 h
      · intro x hx
        obtain ⟨y, _, hy⟩ := hmatched x hx
        exact ⟨(x, y), Finset.mem_filter.mpr ⟨hy, hx⟩, rfl⟩
    rw [hMT, Finset.card_image_of_injOn, h1]
    intro e he e' he' h
    exact hM2 e (Finset.mem_filter.mp he).1 e' (Finset.mem_filter.mp he').1 h
  have hsub : MT ⊆ nbhd E T := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := (hmemMT y).mp hy
    unfold nbhd
    rw [Finset.mem_image]
    exact ⟨(x, y), Finset.mem_filter.mpr ⟨hMsub hxy, hx⟩, rfl⟩
  -- key: an extra neighbour
  have key : ∀ y, AltReach E Mt Y y → ∀ x, (x, y) ∈ Mt → x ∈ T → ∃ y'' ∈ nbhd E T, y'' ∉ MT := by
    intro y hy
    induction hy with
    | unsat hyY hyun =>
      intro x hx _
      exact absurd hx (hyun x)
    | @step y y' x hy0 hxy hxyM hxy' ih =>
      intro x'' hx'' hxT
      have hxx : x'' = x := by
        have := hM2 _ hx'' _ hxy' rfl
        exact (Prod.mk.inj this).1
      subst hxx
      have hynb : y ∈ nbhd E T := by
        unfold nbhd
        rw [Finset.mem_image]
        exact ⟨(x'', y), Finset.mem_filter.mpr ⟨hxy, hxT⟩, rfl⟩
      by_cases hmate : ∃ x₀, (x₀, y) ∈ Mt
      · obtain ⟨x₀, hx₀⟩ := hmate
        by_cases hx₀T : x₀ ∈ T
        · exact ih x₀ hx₀ hx₀T
        · refine ⟨y, hynb, fun hyMT => ?_⟩
          obtain ⟨x₁, hx₁, hx₁y⟩ := (hmemMT y).mp hyMT
          have := hM2 _ hx₁y _ hx₀ rfl
          exact hx₀T ((Prod.mk.inj this).1 ▸ hx₁)
      · refine ⟨y, hynb, fun hyMT => ?_⟩
        obtain ⟨x₁, _, hx₁y⟩ := (hmemMT y).mp hyMT
        exact hmate ⟨x₁, hx₁y⟩
  obtain ⟨x₀, hx₀⟩ := hTne
  obtain ⟨y₀, hy₀r, hy₀⟩ := hmatched x₀ hx₀
  obtain ⟨y'', hy''nb, hy''MT⟩ := key y₀ hy₀r x₀ hy₀ hx₀
  rw [← hcard]
  exact Finset.card_lt_card ⟨hsub, fun hh => hy''MT (hh hy''nb)⟩

theorem solution {α β : Type*} [DecidableEq α] [DecidableEq β]
    (X : Finset α) (Y : Finset β) (E : Finset (α × β)) (hE : E ⊆ X ×ˢ Y)
    (Mt : Finset (α × β)) (hM : IsMaxMatching E Mt) :
    FH E Mt X Y = ∅ ↔ ∀ T ⊆ X, T.Nonempty → T.card < (nbhd E T).card := by
  classical
  obtain ⟨hMsub, hM1, hM2⟩ := hM.1
  have memN : ∀ (T : Finset α) y, y ∈ nbhd E T ↔ ∃ x ∈ T, (x, y) ∈ E := by
    intro T y
    unfold nbhd
    rw [Finset.mem_image]
    constructor
    · rintro ⟨e, he, rfl⟩
      obtain ⟨heE, heT⟩ := Finset.mem_filter.mp he
      exact ⟨e.1, heT, heE⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨(x, y), Finset.mem_filter.mpr ⟨hxy, hx⟩, rfl⟩
  constructor
  · intro hF T hT hne
    refine ims_l36 X Y E hE Mt hM T ?_ hne
    rw [hF]
    simpa using hT
  · intro hall
    -- Step A: every vertex of X is matched
    have hA : ∀ x ∈ X, ∃ y, (x, y) ∈ Mt := by
      let t : ↥X → Finset β := fun x => nbhd E {x.1}
      have hHall : ∀ s : Finset ↥X, s.card ≤ (s.biUnion t).card := by
        intro s
        rcases s.eq_empty_or_nonempty with rfl | hs
        · simp
        · have hsub : s.map (Function.Embedding.subtype _) ⊆ X := by
            intro x hx
            rw [Finset.mem_map] at hx
            obtain ⟨a, _, rfl⟩ := hx
            exact a.2
          have h1 := hall (s.map (Function.Embedding.subtype _)) hsub (by simpa using hs)
          have h2 : nbhd E (s.map (Function.Embedding.subtype _)) = s.biUnion t := by
            ext y
            rw [memN, Finset.mem_biUnion]
            constructor
            · rintro ⟨x, hx, hxy⟩
              rw [Finset.mem_map] at hx
              obtain ⟨a, ha, rfl⟩ := hx
              exact ⟨a, ha, (memN _ _).mpr ⟨a.1, Finset.mem_singleton_self _, hxy⟩⟩
            · rintro ⟨a, ha, hy⟩
              obtain ⟨x, hx, hxy⟩ := (memN _ _).mp hy
              rw [Finset.mem_singleton] at hx
              subst hx
              exact ⟨a.1, Finset.mem_map.mpr ⟨a, ha, rfl⟩, hxy⟩
          rw [h2, Finset.card_map] at h1
          exact h1.le
      obtain ⟨f, hfinj, hf⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hHall
      let M₁ : Finset (α × β) := (Finset.univ : Finset ↥X).image (fun x => (x.1, f x))
      have hM₁ : IsMatching E M₁ := by
        refine ⟨?_, ?_, ?_⟩
        · intro e he
          obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp he
          obtain ⟨x', hx', hxy⟩ := (memN _ _).mp (hf x)
          rw [Finset.mem_singleton] at hx'
          rw [hx'] at hxy
          exact hxy
        · intro e he e' he' h
          obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp he
          obtain ⟨x', _, rfl⟩ := Finset.mem_image.mp he'
          have : x = x' := Subtype.ext h
          rw [this]
        · intro e he e' he' h
          obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp he
          obtain ⟨x', _, rfl⟩ := Finset.mem_image.mp he'
          have : x = x' := hfinj h
          rw [this]
      have hcard₁ : M₁.card = X.card := by
        rw [Finset.card_image_of_injective _ (fun x x' h => Subtype.ext (congrArg Prod.fst h))]
        simp
      have hle := hM.2 M₁ hM₁
      have hMfst : Mt.image Prod.fst ⊆ X := by
        intro x hx
        obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
        exact (Finset.mem_product.mp (hE (hMsub he))).1
      have hcardM : (Mt.image Prod.fst).card = Mt.card :=
        Finset.card_image_of_injOn (fun e he e' he' h => hM1 e he e' he' h)
      have heq : Mt.image Prod.fst = X :=
        Finset.eq_of_subset_of_card_le hMfst (by rw [hcardM]; omega)
      intro x hx
      rw [← heq] at hx
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨e.2, he⟩
    -- Step B: every vertex of X is matched to a reachable vertex
    by_contra hne
    obtain ⟨x₀, hx₀⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    set T : Finset α := X.filter (fun x => ¬ ∃ y, AltReach E Mt Y y ∧ (x, y) ∈ Mt) with hT
    have hTX : T ⊆ X := Finset.filter_subset _ _
    have hx₀T : x₀ ∈ T := by
      simp only [FH, Finset.mem_filter] at hx₀
      exact Finset.mem_filter.mpr hx₀
    have hTmem : ∀ x, x ∈ T ↔ x ∈ X ∧ ¬ ∃ y, AltReach E Mt Y y ∧ (x, y) ∈ Mt := by
      intro x; rw [hT, Finset.mem_filter]
    have h1 := hall T hTX ⟨x₀, hx₀T⟩
    -- the neighbourhood of T consists of mates of T
    set MT : Finset β := (Mt.filter (fun e => e.1 ∈ T)).image Prod.snd with hMT
    have hsub : nbhd E T ⊆ MT := by
      intro y hy
      obtain ⟨x, hxT, hxy⟩ := (memN _ _).mp hy
      obtain ⟨hxX, hxn⟩ := (hTmem x).mp hxT
      have hyY : y ∈ Y := (Finset.mem_product.mp (hE hxy)).2
      -- y is not reachable
      have hyr : ¬ AltReach E Mt Y y := by
        intro hr
        obtain ⟨yx, hyx⟩ := hA x hxX
        by_cases hxyM : (x, y) ∈ Mt
        · exact hxn ⟨y, hr, hxyM⟩
        · exact hxn ⟨yx, AltReach.step hr hxy hxyM hyx, hyx⟩
      -- so y is matched
      have hmate : ∃ x'', (x'', y) ∈ Mt := by
        by_contra hno
        push_neg at hno
        exact hyr (AltReach.unsat hyY hno)
      obtain ⟨x'', hx''⟩ := hmate
      have hx''T : x'' ∈ T := by
        rw [hTmem]
        refine ⟨(Finset.mem_product.mp (hE (hMsub hx''))).1, ?_⟩
        rintro ⟨y', hy'r, hy'⟩
        have := hM1 _ hx'' _ hy' rfl
        have hyy : y = y' := (Prod.mk.inj this).2
        exact hyr (hyy ▸ hy'r)
      rw [hMT, Finset.mem_image]
      exact ⟨(x'', y), Finset.mem_filter.mpr ⟨hx'', hx''T⟩, rfl⟩
    have h2 : MT.card ≤ T.card := by
      refine (Finset.card_image_le).trans ?_
      refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
      · intro e he
        exact (Finset.mem_filter.mp he).2
      · intro e he e' he' h
        exact hM1 e (Finset.mem_filter.mp he).1 e' (Finset.mem_filter.mp he').1 h
    have h3 := Finset.card_le_card hsub
    omega
