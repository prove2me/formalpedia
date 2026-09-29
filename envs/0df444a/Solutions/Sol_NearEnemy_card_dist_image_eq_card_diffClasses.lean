-- Prove2me | solution 1 for NearEnemy.card_dist_image_eq_card_diffClasses
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-18T15:00:06.095064+00:00
-- url     : https://prove2.me/submissions/ec6e6443-7f36-43c1-9fd6-b7c76379c8bb

import Mathlib
import Definitions.Def_NearEnemyDefs
import Theorems.Thm_NearEnemy_dist_image_eq_iff_of_sep

universe u_1
open scoped RealInnerProductSpace
open scoped Classical
open MvPolynomial
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]
open NearEnemy
namespace NearEnemy

omit [Fintype ι] in
/-- The separation property forces injectivity on `G`: take `c = e = a` in
`hsep`. -/
 theorem injOn_of_sep
    {G : Finset (EuclideanSpace ℝ ι)}
    {T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)}
    (hsep : ∀ a ∈ G, ∀ b ∈ G, ∀ c ∈ G, ∀ e ∈ G,
      a - b ≠ c - e → a - b ≠ -(c - e) →
      dist (T a) (T b) ≠ dist (T c) (T e)) :
    ∀ a ∈ G, ∀ b ∈ G, a ≠ b → T a ≠ T b := by
  intro a ha b hb hab h
  refine hsep a ha b hb a ha a ha ?_ ?_ (by rw [h])
  · rw [sub_self]
    exact sub_ne_zero.mpr hab
  · rw [sub_self, neg_zero]
    exact sub_ne_zero.mpr hab

end NearEnemy

open NearEnemy in
theorem solution {G : Finset (EuclideanSpace ℝ ι)}
    {T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)}
    (hsep : ∀ a ∈ G, ∀ b ∈ G, ∀ c ∈ G, ∀ e ∈ G,
      a - b ≠ c - e → a - b ≠ -(c - e) →
      dist (T a) (T b) ≠ dist (T c) (T e)) :
    (((G.image fun x ↦ T x).offDiag).image fun q ↦ dist q.1 q.2).card =
      ((G.offDiag).image fun p ↦
        ({p.1 - p.2, p.2 - p.1} : Finset (EuclideanSpace ℝ ι))).card := by
  -- the downstairs distance set is indexed by upstairs off-diagonal pairs
  have himg : (((G.image fun x ↦ T x).offDiag).image fun q ↦ dist q.1 q.2) =
      (G.offDiag).image fun p ↦ dist (T p.1) (T p.2) := by
    ext d
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨⟨q₁, q₂⟩, hq, rfl⟩
      obtain ⟨hq₁, hq₂, hne⟩ := Finset.mem_offDiag.mp hq
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq₁
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq₂
      exact ⟨(a, b),
        Finset.mem_offDiag.mpr ⟨ha, hb, fun h ↦ hne (congrArg _ h)⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, hab, rfl⟩
      obtain ⟨ha, hb, hne⟩ := Finset.mem_offDiag.mp hab
      exact ⟨(T a, T b),
        Finset.mem_offDiag.mpr ⟨Finset.mem_image_of_mem _ ha,
          Finset.mem_image_of_mem _ hb, injOn_of_sep hsep a ha b hb hne⟩,
        rfl⟩
  -- two distances agree iff the two ±difference classes agree
  have key : ∀ p ∈ G.offDiag, ∀ q ∈ G.offDiag,
      dist (T p.1) (T p.2) = dist (T q.1) (T q.2) ↔
        ({p.1 - p.2, p.2 - p.1} : Finset (EuclideanSpace ℝ ι)) =
          {q.1 - q.2, q.2 - q.1} := by
    intro p hp q hq
    obtain ⟨hp1, hp2, -⟩ := Finset.mem_offDiag.mp hp
    obtain ⟨hq1, hq2, -⟩ := Finset.mem_offDiag.mp hq
    rw [dist_image_eq_iff_of_sep hsep hp1 hp2 hq1 hq2]
    constructor
    · rintro (h | h)
      · have h' : p.2 - p.1 = q.2 - q.1 := by
          rw [← neg_sub p.1 p.2, ← neg_sub q.1 q.2, h]
        rw [h, h']
      · have h1 : p.1 - p.2 = q.2 - q.1 := by rw [h, neg_sub]
        have h2 : p.2 - p.1 = q.1 - q.2 := by
          rw [← neg_sub p.1 p.2, h1, neg_sub]
        rw [h1, h2, Finset.pair_comm]
    · intro h
      have hmem : p.1 - p.2 ∈ ({q.1 - q.2, q.2 - q.1} :
          Finset (EuclideanSpace ℝ ι)) := h ▸ Finset.mem_insert_self _ _
      rcases Finset.mem_insert.mp hmem with h' | h'
      · exact Or.inl h'
      · exact Or.inr (by rw [Finset.mem_singleton.mp h', neg_sub])
  -- both counts equal the count of the joint (distance, class) image
  rw [himg]
  set pairF : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι →
      ℝ × Finset (EuclideanSpace ℝ ι) :=
    fun p ↦ (dist (T p.1) (T p.2), {p.1 - p.2, p.2 - p.1}) with hpairF
  have hfst : Set.InjOn
      (Prod.fst : ℝ × Finset (EuclideanSpace ℝ ι) → ℝ)
      ↑((G.offDiag).image pairF) := by
    intro x hx y hy hxy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
    simp only [hpairF, Prod.mk.injEq]
    exact ⟨hxy, (key p hp q hq).mp hxy⟩
  have hsnd : Set.InjOn
      (Prod.snd : ℝ × Finset (EuclideanSpace ℝ ι) →
        Finset (EuclideanSpace ℝ ι))
      ↑((G.offDiag).image pairF) := by
    intro x hx y hy hxy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
    simp only [hpairF, Prod.mk.injEq]
    exact ⟨(key p hp q hq).mpr hxy, hxy⟩
  calc ((G.offDiag).image fun p ↦ dist (T p.1) (T p.2)).card
      = (((G.offDiag).image pairF).image Prod.fst).card := by
        rw [Finset.image_image]
        rfl
    _ = ((G.offDiag).image pairF).card :=
        Finset.card_image_of_injOn hfst
    _ = (((G.offDiag).image pairF).image Prod.snd).card :=
        (Finset.card_image_of_injOn hsnd).symm
    _ = ((G.offDiag).image fun p ↦
          ({p.1 - p.2, p.2 - p.1} : Finset (EuclideanSpace ℝ ι))).card := by
        rw [Finset.image_image]
        rfl
