-- Prove2me | solution 1 for ImprovedMMS.Additive.corollary_3_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T03:55:45.872983+00:00
-- url     : https://prove2.me/submissions/8f3fa2f7-0bd5-4ae7-831d-e877b41b4146

import Mathlib
import Definitions.Def_ImprovedMMS_Additive_Bipartite
import Theorems.Thm_ImprovedMMS_Additive_lemma_3_7

set_option autoImplicit false
open ImprovedMMS.Additive

/-- Alternating reachability with bounded depth. -/
def cor38RK {α β : Type*} (E Mt : Finset (α × β)) (Y : Finset β) : ℕ → β → Prop
  | 0, y => y ∈ Y ∧ ∀ x : α, (x, y) ∉ Mt
  | k + 1, y' => cor38RK E Mt Y k y' ∨
      ∃ (y : β) (x : α), cor38RK E Mt Y k y ∧ (x, y) ∈ E ∧ (x, y) ∉ Mt ∧ (x, y') ∈ Mt

theorem cor38RK_mono {α β : Type*} (E Mt : Finset (α × β)) (Y : Finset β) (j k : ℕ)
    (hjk : j ≤ k) (w : β) (h : cor38RK E Mt Y j w) : cor38RK E Mt Y k w := by
  induction k, hjk using Nat.le_induction with
  | base => exact h
  | succ k _ ih => exact Or.inl ih

theorem cor38RK_of_altReach {α β : Type*} (E Mt : Finset (α × β)) (Y : Finset β) (y : β)
    (h : AltReach E Mt Y y) : ∃ k, cor38RK E Mt Y k y := by
  induction h with
  | unsat hy hun => exact ⟨0, hy, hun⟩
  | @step y y' x _ hxy hxyM hxy' ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, Or.inr ⟨y, x, hk, hxy, hxyM, hxy'⟩⟩

/-- Augmenting path: an unsaturated `x` adjacent to an alternately reachable `y` yields a
larger matching. -/
theorem cor38_augment {α β : Type*} [DecidableEq α] [DecidableEq β]
    (E : Finset (α × β)) (Y : Finset β) :
    ∀ k : ℕ, ∀ Mt : Finset (α × β), IsMatching E Mt → ∀ y, cor38RK E Mt Y k y →
      ∀ x : α, (∀ z, (x, z) ∉ Mt) → (x, y) ∈ E →
        ∃ M' : Finset (α × β), IsMatching E M' ∧ M'.card = Mt.card + 1 := by
  intro k
  induction k with
  | zero =>
    intro Mt hM y hy x hx hxy
    obtain ⟨hyY, hyun⟩ := hy
    obtain ⟨hsub, h1, h2⟩ := hM
    have hnot : (x, y) ∉ Mt := hx y
    refine ⟨insert (x, y) Mt, ⟨?_, ?_, ?_⟩, Finset.card_insert_of_notMem hnot⟩
    · intro e he
      rcases Finset.mem_insert.mp he with rfl | he
      · exact hxy
      · exact hsub he
    · intro e he e' he' h
      rcases Finset.mem_insert.mp he with rfl | he <;>
        rcases Finset.mem_insert.mp he' with rfl | he'
      · rfl
      · exact absurd (show (e'.1, e'.2) ∈ Mt from he') (by rw [← h]; exact hx _)
      · exact absurd (show (e.1, e.2) ∈ Mt from he) (by rw [h]; exact hx _)
      · exact h1 e he e' he' h
    · intro e he e' he' h
      rcases Finset.mem_insert.mp he with rfl | he <;>
        rcases Finset.mem_insert.mp he' with rfl | he'
      · rfl
      · exact absurd (show (e'.1, e'.2) ∈ Mt from he') (by rw [← h]; exact hyun _)
      · exact absurd (show (e.1, e.2) ∈ Mt from he) (by rw [h]; exact hyun _)
      · exact h2 e he e' he' h
  | succ k ih =>
    intro Mt hM y' hy' x hx hxy'
    by_cases hk : cor38RK E Mt Y k y'
    · exact ih Mt hM y' hk x hx hxy'
    rcases hy' with hy' | ⟨y, x1, hy, hx1y, hx1yM, hx1y'⟩
    · exact absurd hy' hk
    obtain ⟨hsub, h1, h2⟩ := hM
    have hxx1 : x ≠ x1 := by
      rintro rfl; exact hx _ hx1y'
    set Mt' : Finset (α × β) := insert (x, y') (Mt.erase (x1, y')) with hMt'
    have hnot : (x, y') ∉ Mt.erase (x1, y') := fun h => hx _ (Finset.mem_of_mem_erase h)
    have hcard : Mt'.card = Mt.card := by
      rw [hMt', Finset.card_insert_of_notMem hnot, Finset.card_erase_of_mem hx1y']
      have : 0 < Mt.card := Finset.card_pos.mpr ⟨_, hx1y'⟩
      omega
    have hM' : IsMatching E Mt' := by
      refine ⟨?_, ?_, ?_⟩
      · intro e he
        rcases Finset.mem_insert.mp he with rfl | he
        · exact hxy'
        · exact hsub (Finset.mem_of_mem_erase he)
      · intro e he e' he' h
        rcases Finset.mem_insert.mp he with rfl | he <;>
          rcases Finset.mem_insert.mp he' with rfl | he'
        · rfl
        · exact absurd (show (e'.1, e'.2) ∈ Mt from Finset.mem_of_mem_erase he')
            (by rw [← h]; exact hx _)
        · exact absurd (show (e.1, e.2) ∈ Mt from Finset.mem_of_mem_erase he)
            (by rw [h]; exact hx _)
        · exact h1 e (Finset.mem_of_mem_erase he) e' (Finset.mem_of_mem_erase he') h
      · intro e he e' he' h
        rcases Finset.mem_insert.mp he with rfl | he <;>
          rcases Finset.mem_insert.mp he' with rfl | he'
        · rfl
        · exfalso
          have hm := Finset.mem_of_mem_erase he'
          have hne := Finset.ne_of_mem_erase he'
          exact hne (h2 _ hm _ hx1y' (by simpa using h.symm))
        · exfalso
          have hm := Finset.mem_of_mem_erase he
          have hne := Finset.ne_of_mem_erase he
          exact hne (h2 _ hm _ hx1y' (by simpa using h))
        · exact h2 e (Finset.mem_of_mem_erase he) e' (Finset.mem_of_mem_erase he') h
    -- reachability is preserved up to depth k
    have hpres : ∀ j ≤ k, ∀ w, cor38RK E Mt Y j w → cor38RK E Mt' Y j w := by
      intro j
      induction j with
      | zero =>
        intro _ w hw
        refine ⟨hw.1, fun z hz => ?_⟩
        rcases Finset.mem_insert.mp hz with h | h
        · have : w = y' := (Prod.mk.inj h).2
          subst this
          exact hk (cor38RK_mono E Mt Y 0 k (Nat.zero_le _) _ hw)
        · exact hw.2 z (Finset.mem_of_mem_erase h)
      | succ j ihj =>
        intro hj w hw
        rcases hw with hw | ⟨ya, xa, hya, hxaE, hxaM, hxaw⟩
        · exact Or.inl (ihj (by omega) w hw)
        · refine Or.inr ⟨ya, xa, ihj (by omega) ya hya, hxaE, ?_, ?_⟩
          · intro hm
            rcases Finset.mem_insert.mp hm with h | h
            · have : ya = y' := (Prod.mk.inj h).2
              subst this
              exact hk (cor38RK_mono E Mt Y j k (by omega) _ hya)
            · exact hxaM (Finset.mem_of_mem_erase h)
          · have hwy : w ≠ y' := by
              rintro rfl
              exact hk (cor38RK_mono E Mt Y (j + 1) k hj _
                (Or.inr ⟨ya, xa, hya, hxaE, hxaM, hxaw⟩))
            refine Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨?_, hxaw⟩)
            intro h; exact hwy (Prod.mk.inj h).2
    have hy' : cor38RK E Mt' Y k y := hpres k le_rfl y hy
    have hx1un : ∀ z, (x1, z) ∉ Mt' := by
      intro z hz
      rcases Finset.mem_insert.mp hz with h | h
      · exact hxx1 (Prod.mk.inj h).1.symm
      · have hm := Finset.mem_of_mem_erase h
        exact Finset.ne_of_mem_erase h (h1 _ hm _ hx1y' rfl)
    obtain ⟨M', hM'm, hM'c⟩ := ih Mt' hM' y hy' x1 hx1un hx1y
    exact ⟨M', hM'm, by rw [hM'c, hcard]⟩

theorem solution {α β : Type*} [DecidableEq α] [DecidableEq β]
    (X : Finset α) (Y : Finset β) (E : Finset (α × β)) (hE : E ⊆ X ×ˢ Y)
    (Mt : Finset (α × β)) (hM : IsMaxMatching E Mt) :
    ∀ M' : Finset (α × β),
      IsMaxMatching (inducedEdges E (X \ FH E Mt X Y) (Y \ nbhd E (FH E Mt X Y))) M' →
      FH (inducedEdges E (X \ FH E Mt X Y) (Y \ nbhd E (FH E Mt X Y))) M'
        (X \ FH E Mt X Y) (Y \ nbhd E (FH E Mt X Y)) = ∅ := by
  classical
  intro M' hM'
  set F := FH E Mt X Y with hF
  set X' := X \ F with hX'
  set Y' := Y \ nbhd E F with hY'
  set E' := inducedEdges E X' Y' with hE'
  obtain ⟨hMsub, hM1, hM2⟩ := hM.1
  have memN : ∀ (E₀ : Finset (α × β)) (T : Finset α) y,
      y ∈ nbhd E₀ T ↔ ∃ x ∈ T, (x, y) ∈ E₀ := by
    intro E₀ T y
    unfold nbhd
    rw [Finset.mem_image]
    constructor
    · rintro ⟨e, he, rfl⟩
      obtain ⟨heE, heT⟩ := Finset.mem_filter.mp he
      exact ⟨e.1, heT, heE⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨(x, y), Finset.mem_filter.mpr ⟨hxy, hx⟩, rfl⟩
  have memF : ∀ x, x ∈ F ↔ x ∈ X ∧ ¬ ∃ y, AltReach E Mt Y y ∧ (x, y) ∈ Mt := by
    intro x
    rw [hF]
    simp only [FH, Finset.mem_filter]
  -- reachable vertices lie in Y
  have hRY : ∀ y, AltReach E Mt Y y → y ∈ Y := by
    intro y h
    induction h with
    | unsat hy _ => exact hy
    | @step y y' x _ _ _ hxy' _ =>
      exact (Finset.mem_product.mp (hE (hMsub hxy'))).2
  -- no vertex of F is adjacent to a reachable vertex
  have hFR : ∀ x ∈ F, ∀ y, (x, y) ∈ E → ¬ AltReach E Mt Y y := by
    intro x hx y hxy hr
    obtain ⟨_, hxn⟩ := (memF x).mp hx
    by_cases hxyM : (x, y) ∈ Mt
    · exact hxn ⟨y, hr, hxyM⟩
    by_cases hmat : ∃ z, (x, z) ∈ Mt
    · obtain ⟨z, hz⟩ := hmat
      exact hxn ⟨z, AltReach.step hr hxy hxyM hz, hz⟩
    · push_neg at hmat
      obtain ⟨k, hk⟩ := cor38RK_of_altReach E Mt Y y hr
      obtain ⟨M'', hM''m, hM''c⟩ := cor38_augment E Y k Mt hM.1 y hk x hmat hxy
      have := hM.2 M'' hM''m
      omega
  have hRY' : ∀ y, AltReach E Mt Y y → y ∈ Y' := by
    intro y hr
    refine Finset.mem_sdiff.mpr ⟨hRY y hr, fun hy => ?_⟩
    obtain ⟨x, hxF, hxy⟩ := (memN E F y).mp hy
    exact hFR x hxF y hxy hr
  have hE'sub : E' ⊆ X' ×ˢ Y' := by
    intro e he
    obtain ⟨_, h1, h2⟩ := Finset.mem_filter.mp he
    exact Finset.mem_product.mpr ⟨h1, h2⟩
  refine (lemma_3_7 X' Y' E' hE'sub M' hM').mpr ?_
  intro T hT hTne
  -- mates of T
  set MT : Finset β := (Mt.filter (fun e => e.1 ∈ T)).image Prod.snd with hMT
  have hmemMT : ∀ y, y ∈ MT ↔ ∃ x ∈ T, (x, y) ∈ Mt := by
    intro y
    simp only [hMT, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨e, ⟨he, hx⟩, rfl⟩
      exact ⟨e.1, hx, he⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨(x, y), ⟨hxy, hx⟩, rfl⟩
  have hmatched : ∀ x ∈ T, ∃ y, AltReach E Mt Y y ∧ (x, y) ∈ Mt := by
    intro x hx
    have := hT hx
    rw [hX', Finset.mem_sdiff] at this
    obtain ⟨hxX, hxF⟩ := this
    by_contra hcon
    exact hxF ((memF x).mpr ⟨hxX, hcon⟩)
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
  -- a reachable neighbour of T in E is a neighbour in E'
  have hnb' : ∀ x ∈ T, ∀ y, (x, y) ∈ E → AltReach E Mt Y y → y ∈ nbhd E' T := by
    intro x hx y hxy hr
    refine (memN E' T y).mpr ⟨x, hx, ?_⟩
    rw [hE']
    exact Finset.mem_filter.mpr ⟨hxy, hT hx, hRY' y hr⟩
  have hsub : MT ⊆ nbhd E' T := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := (hmemMT y).mp hy
    obtain ⟨y₁, hy₁r, hy₁⟩ := hmatched x hx
    have : y = y₁ := (Prod.mk.inj (hM1 _ hxy _ hy₁ rfl)).2
    subst this
    exact hnb' x hx y (hMsub hxy) hy₁r
  have key : ∀ y, AltReach E Mt Y y → ∀ x, (x, y) ∈ Mt → x ∈ T →
      ∃ y'' ∈ nbhd E' T, y'' ∉ MT := by
    intro y hy
    induction hy with
    | unsat _ hyun =>
      intro x hx _
      exact absurd hx (hyun x)
    | @step y y' x hy0 hxy hxyM hxy' ih =>
      intro x'' hx'' hxT
      have hxx : x'' = x := by
        have := hM2 _ hx'' _ hxy' rfl
        exact (Prod.mk.inj this).1
      subst hxx
      have hynb : y ∈ nbhd E' T := hnb' x'' hxT y hxy hy0
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
