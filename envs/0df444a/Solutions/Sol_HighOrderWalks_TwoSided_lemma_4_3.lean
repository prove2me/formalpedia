-- Prove2me | solution 1 for HighOrderWalks.TwoSided.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T06:22:45.0702+00:00
-- url     : https://prove2.me/submissions/ebb9c600-e23f-4e57-95ab-967e66a984c5

import Mathlib
import Definitions.Def_HighOrderWalks_TwoSided_Setting
import Definitions.Def_HighOrderWalks_TwoSided_Subspaces

/- Supporting proof by sometik179, accepted Prove2Me submission aef2bebc-0500-4ad9-b6a3-d4bb8479530e, Apache 2.0. -/


section
noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
theorem mem_cells {X : Finset (Finset V)} {c : ℕ} {σ : Finset V} :
    σ ∈ cells X c ↔ σ ∈ X ∧ σ.card = c := by simp [cells]

omit [DecidableEq V] in
theorem supp_iff {X : Finset (Finset V)} {c : ℕ} {f : Finset V → ℝ} :
    Supp X c f ↔ ∀ σ, σ ∉ cells X c → f σ = 0 := by
  constructor
  · intro h σ hs
    by_contra hn
    exact hs (h σ hn)
  · intro h σ hn
    by_contra hs
    exact hn (h σ hs)

theorem dS_support {X : Finset (Finset V)} {c : ℕ} {f : Finset V → ℝ}
    (hf : Supp X c f) : Supp X (c + 1) (dS X f) := by
  rw [supp_iff]
  intro σ hσ
  unfold dS
  split_ifs with hx
  · apply Finset.sum_eq_zero
    intro τ hτ
    have ht := (Finset.mem_filter.mp hτ).2
    apply (supp_iff.mp hf) τ
    intro hc
    have hc' := mem_cells.mp hc
    exact hσ (mem_cells.mpr ⟨hx, by omega⟩)
  · rfl

theorem dStar_support {X : Finset (Finset V)} {m : Finset V → ℝ}
    {c : ℕ} {f : Finset V → ℝ} (hf : Supp X (c + 1) f) :
    Supp X c (dStar X m f) := by
  rw [supp_iff]
  intro τ hτ
  unfold dStar
  split_ifs with hx
  · apply Finset.sum_eq_zero
    intro σ hσ
    have hs := (Finset.mem_filter.mp hσ).2
    have hz : f σ = 0 := by
      apply (supp_iff.mp hf) σ
      intro hc
      have hc' := mem_cells.mp hc
      exact hτ (mem_cells.mpr ⟨hx, by omega⟩)
    rw [hz, mul_zero]
  · rfl

omit [DecidableEq V] in
theorem ip_symm (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ)
    (f g : Finset V → ℝ) : ip X m c f g = ip X m c g f := by
  unfold ip
  apply Finset.sum_congr rfl
  intro σ _
  ring

end HighOrderWalks.TwoSided.Fresh
end


section
noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

theorem dS_cell {X : Finset (Finset V)} {c : ℕ} {σ : Finset V}
    (hσ : σ ∈ cells X (c + 1)) (f : Finset V → ℝ) :
    dS X f σ = ∑ τ ∈ cells X c, if τ ⊆ σ then f τ else 0 := by
  have h := mem_cells.mp hσ
  have he : X.filter (fun τ => τ ⊆ σ ∧ τ.card + 1 = σ.card) =
      (cells X c).filter (fun τ => τ ⊆ σ) := by
    ext τ
    simp [cells, h.2, and_comm]
    tauto
  simp only [dS, if_pos h.1, he, Finset.sum_filter]

theorem dStar_cell {X : Finset (Finset V)} {m : Finset V → ℝ}
    {c : ℕ} {τ : Finset V} (hτ : τ ∈ cells X c) (f : Finset V → ℝ) :
    dStar X m f τ = ∑ σ ∈ cells X (c + 1), if τ ⊆ σ then m σ / m τ * f σ else 0 := by
  have h := mem_cells.mp hτ
  have he : X.filter (fun σ => τ ⊆ σ ∧ σ.card = τ.card + 1) =
      (cells X (c + 1)).filter (fun σ => τ ⊆ σ) := by
    ext σ
    simp [cells, h.2, and_comm]
    tauto
  simp only [dStar, if_pos h.1, he, Finset.sum_filter]

theorem incidence_adjoint (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ)
    (hm : ∀ τ ∈ cells X c, m τ ≠ 0) (f g : Finset V → ℝ) :
    ip X m (c + 1) (dS X f) g = ip X m c f (dStar X m g) := by
  calc
    ip X m (c + 1) (dS X f) g =
        ∑ σ ∈ cells X (c + 1), ∑ τ ∈ cells X c,
          if τ ⊆ σ then m σ * f τ * g σ else 0 := by
      unfold ip
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [dS_cell hσ]
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro τ _
      split_ifs <;> ring
    _ = ∑ τ ∈ cells X c, ∑ σ ∈ cells X (c + 1),
          if τ ⊆ σ then m σ * f τ * g σ else 0 := Finset.sum_comm
    _ = ip X m c f (dStar X m g) := by
      unfold ip
      apply Finset.sum_congr rfl
      intro τ hτ
      rw [dStar_cell hτ, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      split_ifs
      · field_simp [hm τ hτ]
      · ring

end HighOrderWalks.TwoSided.Fresh
end


section
noncomputable section
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh

lemma immediate_subfaces_card {V : Type*} [DecidableEq V]
    (X : Finset (Finset V)) (n : ℕ) (hX : IsPureComplex X n)
    (σ : Finset V) (hσ : σ ∈ X) (hne : σ.Nonempty) :
    (X.filter (fun τ => τ ⊆ σ ∧ τ.card + 1 = σ.card)).card = σ.card := by
  have hp : 0 < σ.card := Finset.card_pos.mpr hne
  have heq : X.filter (fun τ => τ ⊆ σ ∧ τ.card + 1 = σ.card) =
      σ.powersetCard (σ.card - 1) := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨_, hsub, hc⟩
      exact ⟨hsub, by omega⟩
    · rintro ⟨hsub, hc⟩
      exact ⟨hX.1 σ hσ τ hsub, hsub, by omega⟩
  rw [heq, Finset.card_powersetCard, Nat.choose_symm (by omega : 1 ≤ σ.card),
    Nat.choose_one_right]

lemma common_immediate_coface_eq_union {V : Type*} [DecidableEq V]
    (s t u : Finset V) (hst : s ≠ t) (hc : s.card = t.card)
    (hsu : s ⊆ u) (htu : t ⊆ u) (hu : u.card = s.card + 1) :
    u = s ∪ t := by
  have hsub : s ∪ t ⊆ u := Finset.union_subset hsu htu
  have hlo : s.card < (s ∪ t).card := by
    by_contra h
    have he : s = s ∪ t := Finset.eq_of_subset_of_card_le
      Finset.subset_union_left (by omega)
    have hts : t ⊆ s := by rw [he]; exact Finset.subset_union_right
    have heq : t = s := Finset.eq_of_subset_of_card_le hts (by omega)
    exact hst heq.symm
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

lemma common_immediate_subface_eq_inter {V : Type*} [DecidableEq V]
    (s t u : Finset V) (hst : s ≠ t) (hc : s.card = t.card)
    (hus : u ⊆ s) (hut : u ⊆ t) (hu : u.card + 1 = s.card) :
    u = s ∩ t := by
  have hsub : u ⊆ s ∩ t := Finset.subset_inter hus hut
  have hhi : (s ∩ t).card < s.card := by
    by_contra h
    have he : s ∩ t = s := Finset.eq_of_subset_of_card_le
      Finset.inter_subset_left (by omega)
    have hst' : s ⊆ t := by rw [← he]; exact Finset.inter_subset_right
    have heq : s = t := Finset.eq_of_subset_of_card_le hst' (by omega)
    exact hst heq
  exact Finset.eq_of_subset_of_card_le hsub (by omega)

end HighOrderWalks.TwoSided.Fresh
end


section
noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

theorem dS_one_cell {X : Finset (Finset V)} {n c : ℕ}
    (hX : IsPureComplex X n) {σ : Finset V} (hσ : σ ∈ cells X (c + 1)) :
    dS X (fun _ => 1) σ = (c + 1 : ℝ) := by
  have hs := mem_cells.mp hσ
  simp only [dS, if_pos hs.1, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [immediate_subfaces_card X n hX σ hs.1 (Finset.card_pos.mp (by omega)), hs.2]
  simp

theorem dStar_one_cell {X : Finset (Finset V)} {n c : ℕ} {m : Finset V → ℝ}
    (hm : IsWeight X n m) (hc : c ≤ n) {τ : Finset V} (hτ : τ ∈ cells X c) :
    dStar X m (fun _ => 1) τ = 1 := by
  have ht := mem_cells.mp hτ
  have he : X.filter (fun σ => τ ⊆ σ ∧ σ.card = τ.card + 1) =
      X.filter (fun σ => σ.card = τ.card + 1 ∧ τ ⊆ σ) := by
    ext σ
    simp only [Finset.mem_filter, and_comm]
  simp only [dStar, if_pos ht.1, mul_one, he]
  rw [← Finset.sum_div, ← hm.2 τ ht.1 (ht.2 ▸ hc)]
  exact div_self (hm.1 τ ht.1).ne'

omit [DecidableEq V] in
theorem ip_congr_right {X : Finset (Finset V)} {m : Finset V → ℝ} {c : ℕ}
    (f : Finset V → ℝ) {g h : Finset V → ℝ}
    (he : ∀ σ ∈ cells X c, g σ = h σ) : ip X m c f g = ip X m c f h := by
  unfold ip
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [he σ hσ]

theorem dS_mean {X : Finset (Finset V)} {n c : ℕ} {m : Finset V → ℝ}
    (hm : IsWeight X n m) (hc : c ≤ n) (f : Finset V → ℝ) :
    ip X m (c + 1) (dS X f) (fun _ => 1) = ip X m c f (fun _ => 1) := by
  rw [incidence_adjoint X m c (fun σ hσ => (hm.1 σ (mem_cells.mp hσ).1).ne')]
  exact ip_congr_right f (fun σ hσ => dStar_one_cell hm hc hσ)

theorem dStar_mean {X : Finset (Finset V)} {n c : ℕ} {m : Finset V → ℝ}
    (hX : IsPureComplex X n) (hm : IsWeight X n m) (f : Finset V → ℝ) :
    ip X m c (dStar X m f) (fun _ => 1) =
      (c + 1 : ℝ) * ip X m (c + 1) f (fun _ => 1) := by
  rw [ip_symm, ← incidence_adjoint X m c
    (fun σ hσ => (hm.1 σ (mem_cells.mp hσ).1).ne'), ip_symm]
  rw [ip_congr_right f (fun σ hσ => dS_one_cell hX hσ)]
  unfold ip
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring

end HighOrderWalks.TwoSided.Fresh
end


section
noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

theorem mem_link {X : Finset (Finset V)} {η τ : Finset V} :
    τ ∈ link X η ↔ τ ∈ X ∧ Disjoint η τ ∧ η ∪ τ ∈ X := by
  simp [link]

theorem link_union_injective (X : Finset (Finset V)) (η : Finset V) :
    Set.InjOn (fun τ => η ∪ τ) (↑(link X η) : Set (Finset V)) := by
  intro τ hτ σ hσ he
  change η ∪ τ = η ∪ σ at he
  have ht := (mem_link.mp hτ).2.1
  have hs := (mem_link.mp hσ).2.1
  apply Finset.ext
  intro v
  have hte : v ∈ τ → v ∉ η := fun hv hη => Finset.disjoint_left.mp ht hη hv
  have hse : v ∈ σ → v ∉ η := fun hv hη => Finset.disjoint_left.mp hs hη hv
  have hv : v ∈ η ∪ τ ↔ v ∈ η ∪ σ := by rw [he]
  simp only [Finset.mem_union] at hv
  tauto

theorem link_image_union {X : Finset (Finset V)} {n : ℕ}
    (hX : IsPureComplex X n) (η : Finset V) :
    (link X η).image (fun τ => η ∪ τ) = X.filter (fun σ => η ⊆ σ) := by
  ext σ
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact ⟨(mem_link.mp hτ).2.2, Finset.subset_union_left⟩
  · rintro ⟨hσ, hησ⟩
    refine ⟨σ \ η, ?_, Finset.union_sdiff_of_subset hησ⟩
    apply mem_link.mpr
    refine ⟨hX.1 σ hσ _ Finset.sdiff_subset, Finset.disjoint_sdiff, ?_⟩
    simpa only [Finset.union_sdiff_of_subset hησ] using hσ

theorem sum_link_union {X : Finset (Finset V)} {n : ℕ}
    (hX : IsPureComplex X n) (η : Finset V) (F : Finset V → ℝ) :
    (∑ τ ∈ link X η, F (η ∪ τ)) = ∑ σ ∈ X.filter (fun σ => η ⊆ σ), F σ := by
  rw [← link_image_union hX η, Finset.sum_image (link_union_injective X η)]

theorem link_union_card {X : Finset (Finset V)} {η τ : Finset V}
    (hτ : τ ∈ link X η) : (η ∪ τ).card = η.card + τ.card :=
  Finset.card_union_of_disjoint (mem_link.mp hτ).2.1

theorem link_subset_iff {X : Finset (Finset V)} {η τ σ : Finset V}
    (hτ : τ ∈ link X η) : η ∪ τ ⊆ η ∪ σ ↔ τ ⊆ σ := by
  constructor
  · intro h v hv
    have hmem := h (Finset.mem_union_right η hv)
    rcases Finset.mem_union.mp hmem with hη | hσ
    · exact False.elim (Finset.disjoint_left.mp (mem_link.mp hτ).2.1 hη hv)
    · exact hσ
  · exact fun h => Finset.union_subset_union_right h

end HighOrderWalks.TwoSided.Fresh
end


section
noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

theorem link_cofaces_image {X : Finset (Finset V)} {n : ℕ}
    (hX : IsPureComplex X n) {η τ : Finset V} (hτ : τ ∈ link X η) :
    ((link X η).filter (fun σ => σ.card = τ.card + 1 ∧ τ ⊆ σ)).image
      (fun σ => η ∪ σ) =
    X.filter (fun σ => σ.card = (η ∪ τ).card + 1 ∧ η ∪ τ ⊆ σ) := by
  ext σ
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨ρ, ⟨hρ, hc, ht⟩, rfl⟩
    refine ⟨(mem_link.mp hρ).2.2, ?_, Finset.union_subset_union_right ht⟩
    rw [link_union_card hρ, link_union_card hτ, hc]
    omega
  · rintro ⟨hσ, hc, ht⟩
    have he : η ⊆ σ := Finset.subset_union_left.trans ht
    have hu : η ∪ (σ \ η) = σ := Finset.union_sdiff_of_subset he
    have hr : σ \ η ∈ link X η := by
      apply mem_link.mpr
      refine ⟨hX.1 σ hσ _ Finset.sdiff_subset, Finset.disjoint_sdiff, ?_⟩
      simpa only [hu] using hσ
    refine ⟨σ \ η, ⟨hr, ?_, ?_⟩, hu⟩
    · have hh := link_union_card hr
      rw [hu] at hh
      rw [link_union_card hτ] at hc
      omega
    · exact (link_subset_iff hτ).mp (hu.symm ▸ ht)

theorem link_isWeight {X : Finset (Finset V)} {n : ℕ} {m : Finset V → ℝ}
    (hX : IsPureComplex X n) (hm : IsWeight X n m) {η : Finset V}
    (hη : η.card ≤ n) : IsWeight (link X η) (n - η.card) (linkWeight m η) := by
  constructor
  · intro τ hτ
    exact hm.1 _ (mem_link.mp hτ).2.2
  · intro τ hτ hc
    change m (η ∪ τ) = _
    rw [hm.2 _ (mem_link.mp hτ).2.2 (by rw [link_union_card hτ]; omega)]
    rw [← link_cofaces_image hX hτ]
    rw [Finset.sum_image]
    · rfl
    · intro a ha b hb he
      exact link_union_injective X η (Finset.mem_filter.mp ha).1
        (Finset.mem_filter.mp hb).1 he

end HighOrderWalks.TwoSided.Fresh
end


section
noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

theorem link_cells_image {X : Finset (Finset V)} {n : ℕ}
    (hX : IsPureComplex X n) (η : Finset V) (c : ℕ) :
    (cells (link X η) c).image (fun τ => η ∪ τ) =
      (cells X (η.card + c)).filter (fun σ => η ⊆ σ) := by
  ext σ
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    have ht := mem_cells.mp hτ
    exact ⟨mem_cells.mpr ⟨(mem_link.mp ht.1).2.2,
      (link_union_card ht.1).trans (congrArg (η.card + ·) ht.2)⟩,
      Finset.subset_union_left⟩
  · rintro ⟨hσ, he⟩
    have hu : η ∪ (σ \ η) = σ := Finset.union_sdiff_of_subset he
    have hr : σ \ η ∈ link X η := by
      apply mem_link.mpr
      refine ⟨hX.1 σ (mem_cells.mp hσ).1 _ Finset.sdiff_subset,
        Finset.disjoint_sdiff, ?_⟩
      simpa only [hu] using (mem_cells.mp hσ).1
    refine ⟨σ \ η, mem_cells.mpr ⟨hr, ?_⟩, hu⟩
    have hh := link_union_card hr
    rw [hu, (mem_cells.mp hσ).2] at hh
    omega

theorem sum_link_cells {X : Finset (Finset V)} {n : ℕ}
    (hX : IsPureComplex X n) (η : Finset V) (c : ℕ) (F : Finset V → ℝ) :
    (∑ τ ∈ cells (link X η) c, F (η ∪ τ)) =
      ∑ σ ∈ cells X (η.card + c), if η ⊆ σ then F σ else 0 := by
  rw [← Finset.sum_filter, ← link_cells_image hX η c, Finset.sum_image]
  intro a ha b hb he
  exact link_union_injective X η (mem_cells.mp ha).1 (mem_cells.mp hb).1 he

theorem localization_ip_sum {X : Finset (Finset V)} {n : ℕ}
    (hX : IsPureComplex X n) (m : Finset V → ℝ) (k : ℕ) (f g : Finset V → ℝ) :
    (∑ η ∈ cells X k, ip (link X η) (linkWeight m η) 1 (loc f η) (loc g η)) =
      (k + 1 : ℝ) * ip X m (k + 1) f g := by
  have he (η : Finset V) (hη : η ∈ cells X k) :
      ip (link X η) (linkWeight m η) 1 (loc f η) (loc g η) =
        ∑ σ ∈ cells X (k + 1), if η ⊆ σ then m σ * f σ * g σ else 0 := by
    unfold ip linkWeight loc
    rw [sum_link_cells hX η 1 (fun σ => m σ * f σ * g σ), (mem_cells.mp hη).2]
  calc
    _ = ∑ η ∈ cells X k, ∑ σ ∈ cells X (k + 1),
        if η ⊆ σ then m σ * f σ * g σ else 0 := Finset.sum_congr rfl he
    _ = ∑ σ ∈ cells X (k + 1), ∑ η ∈ cells X k,
        if η ⊆ σ then m σ * f σ * g σ else 0 := Finset.sum_comm
    _ = _ := by
      unfold ip
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ hσ
      have hs := mem_cells.mp hσ
      have hf : (cells X k).filter (fun η => η ⊆ σ) =
          X.filter (fun η => η ⊆ σ ∧ η.card + 1 = σ.card) := by
        ext η
        simp [cells, hs.2]
        tauto
      rw [← Finset.sum_filter, Finset.sum_const, hf,
        immediate_subfaces_card X n hX σ hs.1 (Finset.card_pos.mp (by omega))]
      simp only [hs.2, Nat.cast_add, Nat.cast_one, nsmul_eq_mul]

end HighOrderWalks.TwoSided.Fresh
end


section
noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

theorem coface_kernel_offdiag {X : Finset (Finset V)} {m : Finset V → ℝ}
    {c : ℕ} {s t : Finset V} (hs : s ∈ cells X c) (ht : t ∈ cells X c)
    (hst : s ≠ t) :
    (∑ u ∈ cells X (c + 1), if s ⊆ u ∧ t ⊆ u then m u else 0) =
      if s ∪ t ∈ cells X (c + 1) then m (s ∪ t) else 0 := by
  have huniq (u : Finset V) (hu : u ∈ cells X (c + 1))
      (h : s ⊆ u ∧ t ⊆ u) : u = s ∪ t :=
    common_immediate_coface_eq_union s t u hst
      ((mem_cells.mp hs).2.trans (mem_cells.mp ht).2.symm) h.1 h.2
      (by rw [(mem_cells.mp hu).2, (mem_cells.mp hs).2])
  by_cases he : s ∪ t ∈ cells X (c + 1)
  · rw [if_pos he, Finset.sum_eq_single (s ∪ t)]
    · simp only [Finset.subset_union_left, Finset.subset_union_right, and_self, if_true]
    · intro u hu hne
      split_ifs with h
      · exact False.elim (hne (huniq u hu h))
      · rfl
    · exact fun h => False.elim (h he)
  · rw [if_neg he]
    apply Finset.sum_eq_zero
    intro u hu
    split_ifs with h
    · exact False.elim (he (huniq u hu h ▸ hu))
    · rfl

theorem coface_kernel_diag {X : Finset (Finset V)} {n c : ℕ} {m : Finset V → ℝ}
    (hm : IsWeight X n m) (hc : c ≤ n) {s : Finset V} (hs : s ∈ cells X c) :
    (∑ u ∈ cells X (c + 1), if s ⊆ u ∧ s ⊆ u then m u else 0) = m s := by
  have he : (cells X (c + 1)).filter (fun u => s ⊆ u) =
      X.filter (fun u => u.card = s.card + 1 ∧ s ⊆ u) := by
    ext u
    simp [cells, (mem_cells.mp hs).2]
    tauto
  simp only [and_self]
  rw [← Finset.sum_filter, he]
  exact (hm.2 s (mem_cells.mp hs).1 (by rw [(mem_cells.mp hs).2]; exact hc)).symm

end HighOrderWalks.TwoSided.Fresh
end


section
noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

theorem dStar_dS_kernel {X : Finset (Finset V)} {m : Finset V → ℝ}
    {c : ℕ} {s : Finset V} (hs : s ∈ cells X c) (f : Finset V → ℝ) :
    dStar X m (dS X f) s =
      ∑ t ∈ cells X c, ((∑ u ∈ cells X (c + 1),
        if s ⊆ u ∧ t ⊆ u then m u else 0) / m s) * f t := by
  rw [dStar_cell hs]
  calc
    _ = ∑ u ∈ cells X (c + 1), ∑ t ∈ cells X c,
        if s ⊆ u ∧ t ⊆ u then m u / m s * f t else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [dS_cell hu]
      by_cases hsu : s ⊆ u
      · simp only [hsu, if_true, Finset.mul_sum, true_and]
        apply Finset.sum_congr rfl
        intro t _
        split_ifs <;> ring
      · simp [hsu]
    _ = ∑ t ∈ cells X c, ∑ u ∈ cells X (c + 1),
        if s ⊆ u ∧ t ⊆ u then m u / m s * f t else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.sum_div, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro u _
      split_ifs <;> ring

end HighOrderWalks.TwoSided.Fresh
end


section
noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

theorem dStar_dS_split {X : Finset (Finset V)} {n c : ℕ} {m : Finset V → ℝ}
    (hm : IsWeight X n m) (hc : c ≤ n) {s : Finset V} (hs : s ∈ cells X c)
    (f : Finset V → ℝ) :
    dStar X m (dS X f) s = f s + ∑ t ∈ cells X c,
      if t ≠ s ∧ s ∪ t ∈ cells X (c + 1) then m (s ∪ t) / m s * f t else 0 := by
  rw [dStar_dS_kernel hs]
  have hh : (∑ t ∈ cells X c, ((∑ u ∈ cells X (c + 1),
      if s ⊆ u ∧ t ⊆ u then m u else 0) / m s) * f t) =
      ∑ t ∈ cells X c, ((if t = s then f s else 0) +
        if t ≠ s ∧ s ∪ t ∈ cells X (c + 1) then m (s ∪ t) / m s * f t else 0) := by
    apply Finset.sum_congr rfl
    intro t ht
    by_cases he : t = s
    · subst t
      rw [coface_kernel_diag hm hc hs]
      simp [div_self (hm.1 s (mem_cells.mp hs).1).ne']
    · rw [coface_kernel_offdiag hs ht (Ne.symm he)]
      split_ifs <;> simp_all
  rw [hh, Finset.sum_add_distrib]
  simp [hs]

theorem upper_identity {X : Finset (Finset V)} {n c : ℕ} {m : Finset V → ℝ}
    (hm : IsWeight X n m) (hc : c ≤ n) {s : Finset V} (hs : s ∈ cells X c)
    (f : Finset V → ℝ) :
    dStar X m (dS X f) s = (c + 1 : ℝ) * upperWalk X m f s := by
  have h := mem_cells.mp hs
  have he : X.filter (fun t => t.card = s.card ∧ t ≠ s ∧ s ∪ t ∈ X ∧
      (s ∪ t).card = s.card + 1) =
      (cells X c).filter (fun t => t ≠ s ∧ s ∪ t ∈ cells X (c + 1)) := by
    ext t
    simp [cells, h.2, and_assoc]
  rw [dStar_dS_split hm hc hs, upperWalk, if_pos h.1, he, Finset.sum_filter,
    h.2, mul_add, Finset.mul_sum]
  congr 1
  · field_simp
  · apply Finset.sum_congr rfl
    intro t _
    split_ifs
    · field_simp
    · ring

end HighOrderWalks.TwoSided.Fresh
end


section
noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

theorem upper_mean {X : Finset (Finset V)} {n c : ℕ} {m : Finset V → ℝ}
    (hX : IsPureComplex X n) (hm : IsWeight X n m) (hc : c ≤ n)
    (f : Finset V → ℝ) :
    ip X m c (upperWalk X m f) (fun _ => 1) = ip X m c f (fun _ => 1) := by
  have hd := dStar_mean hX hm (c := c) (dS X f)
  rw [dS_mean hm hc f] at hd
  have he : ip X m c (dStar X m (dS X f)) (fun _ => 1) =
      (c + 1 : ℝ) * ip X m c (upperWalk X m f) (fun _ => 1) := by
    unfold ip
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [upper_identity hm hc hs]
    ring
  rw [he] at hd
  exact (mul_left_cancel₀ (by positivity : (c + 1 : ℝ) ≠ 0)) hd

theorem nonLazy_mean {X : Finset (Finset V)} {n c : ℕ} {m : Finset V → ℝ}
    (hX : IsPureComplex X n) (hm : IsWeight X n m) (hc : c ≤ n) (hc0 : 0 < c)
    (f : Finset V → ℝ) :
    ip X m c (nonLazyWalk X m f) (fun _ => 1) = ip X m c f (fun _ => 1) := by
  have he : ip X m c (nonLazyWalk X m f) (fun _ => 1) =
      ((c + 1 : ℝ) / c) * ip X m c (upperWalk X m f) (fun _ => 1) -
        ip X m c f (fun _ => 1) / c := by
    unfold ip
    rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    have h := mem_cells.mp hs
    simp only [nonLazyWalk, if_pos h.1, h.2]
    ring
  rw [he, upper_mean hX hm hc]
  have hcne : (c : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hc0)
  field_simp [hcne]
  ring

end HighOrderWalks.TwoSided.Fresh
end


section
noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

def upperLinear (X : Finset (Finset V)) (m : Finset V → ℝ) :
    (Finset V → ℝ) →ₗ[ℝ] (Finset V → ℝ) where
  toFun := upperWalk X m
  map_add' f g := by
    funext s
    by_cases hs : s ∈ X <;> simp [upperWalk, hs, add_div, mul_add,
      Finset.sum_add_distrib]
    ring
  map_smul' a f := by
    funext s
    by_cases hs : s ∈ X <;> simp [upperWalk, hs, Finset.mul_sum, mul_add,
      mul_div_assoc, mul_left_comm]

def nonLazyLinear (X : Finset (Finset V)) (m : Finset V → ℝ) :
    (Finset V → ℝ) →ₗ[ℝ] (Finset V → ℝ) where
  toFun := nonLazyWalk X m
  map_add' f g := by
    funext s
    have hh := congrFun ((upperLinear X m).map_add f g) s
    change upperWalk X m (f + g) s = upperWalk X m f s + upperWalk X m g s at hh
    by_cases hs : s ∈ X <;> simp [nonLazyWalk, hs, hh, add_div, mul_add]
    ring
  map_smul' a f := by
    funext s
    have hh := congrFun ((upperLinear X m).map_smul a f) s
    change upperWalk X m (a • f) s = a * upperWalk X m f s at hh
    by_cases hs : s ∈ X <;> simp [nonLazyWalk, hs, hh]
    ring

end HighOrderWalks.TwoSided.Fresh
end


section
noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh

lemma vertex_lowerWalk_mean {V : Type*} [DecidableEq V]
    (X : Finset (Finset V)) (m f : Finset V → ℝ)
    (τ : Finset V) (hτ : τ ∈ cells X 1) (hempty : (∅ : Finset V) ∈ X) :
    lowerWalk X m f τ = (∑ σ ∈ cells X 1, m σ * f σ) / m ∅ := by
  have hτX := (mem_cells.mp hτ).1
  have hcard := (mem_cells.mp hτ).2
  have hdiag : X.filter (fun η => η ⊆ τ ∧ η.card + 1 = τ.card) = {∅} := by
    ext η
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨_, _, hc⟩
      exact Finset.card_eq_zero.mp (by omega)
    · rintro rfl
      exact ⟨hempty, Finset.empty_subset _, by simp [hcard]⟩
  have hinter (σ : Finset V) (hc : σ.card = 1) (hne : σ ≠ τ) : τ ∩ σ = ∅ := by
    obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hcard
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hc
    subst τ
    subst σ
    have huv : u ≠ v := by intro h; subst v; exact hne rfl
    simp [huv]
  have hoff : X.filter (fun σ => σ.card = τ.card ∧ σ ≠ τ ∧ τ ∩ σ ∈ X ∧
      (τ ∩ σ).card + 1 = τ.card) = (cells X 1).erase τ := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hσX, hc, hne, _, _⟩
      exact ⟨hne, mem_cells.mpr ⟨hσX, hc.trans hcard⟩⟩
    · rintro ⟨hne, hσ⟩
      have hc := (mem_cells.mp hσ).2
      have hi := hinter σ hc hne
      exact ⟨(mem_cells.mp hσ).1, hc.trans hcard.symm, hne,
        by simpa [hi] using hempty, by simp [hi, hcard]⟩
  unfold lowerWalk
  rw [if_pos hτX, hdiag, hoff]
  simp only [Finset.sum_singleton, hcard, Nat.cast_one, one_mul]
  have hsum : (∑ σ ∈ (cells X 1).erase τ, m σ / m (τ ∩ σ) * f σ) =
      (∑ σ ∈ (cells X 1).erase τ, m σ * f σ) / m ∅ := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro σ hσ
    have hm := Finset.mem_erase.mp hσ
    rw [hinter σ (mem_cells.mp hm.2).2 hm.1]
    ring
  rw [hsum]
  have hs := Finset.add_sum_erase (cells X 1) (fun σ => m σ * f σ) hτ
  rw [← hs]
  ring

end HighOrderWalks.TwoSided.Fresh
end


section
noncomputable section
open scoped BigOperators
namespace HighOrderWalks.TwoSided.Fresh

theorem weighted_center_zero {ι : Type*} (s : Finset ι) (w f : ι → ℝ) (a : ℝ)
    (ha : a * ∑ i ∈ s, w i = ∑ i ∈ s, w i * f i) :
    (∑ i ∈ s, w i * (f i - a)) = 0 := by
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  nlinarith [ha]

theorem weighted_center_square {ι : Type*} (s : Finset ι) (w f : ι → ℝ) (a : ℝ)
    (ha : a * ∑ i ∈ s, w i = ∑ i ∈ s, w i * f i) :
    (∑ i ∈ s, w i * (f i - a) ^ 2) =
      (∑ i ∈ s, w i * f i ^ 2) - a ^ 2 * ∑ i ∈ s, w i := by
  have he : (∑ i ∈ s, w i * (f i - a) ^ 2) =
      (∑ i ∈ s, w i * f i ^ 2) - 2 * a * (∑ i ∈ s, w i * f i) +
        a ^ 2 * (∑ i ∈ s, w i) := by
    calc
      _ = ∑ i ∈ s, (w i * f i ^ 2 - (2*a) * (w i*f i) + a^2*w i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
  rw [he, ← ha]
  ring

theorem weighted_center_contract {ι : Type*} (s : Finset ι) (w f : ι → ℝ) (a : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (ha : a * ∑ i ∈ s, w i = ∑ i ∈ s, w i * f i) :
    (∑ i ∈ s, w i * (f i - a) ^ 2) ≤ ∑ i ∈ s, w i * f i ^ 2 := by
  rw [weighted_center_square s w f a ha]
  exact sub_le_self _ (mul_nonneg (sq_nonneg a) (Finset.sum_nonneg hw))

end HighOrderWalks.TwoSided.Fresh
end


section
noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

theorem vertex_mass {X : Finset (Finset V)} {n : ℕ} {m : Finset V → ℝ}
    (hm : IsWeight X n m) (he : (∅ : Finset V) ∈ X) :
    ∑ σ ∈ cells X 1, m σ = m ∅ := by
  have h := hm.2 ∅ he (by simp)
  simpa only [Finset.card_empty, zero_add, Finset.empty_subset, and_true, cells] using h.symm

theorem vertex_center_mean {X : Finset (Finset V)} {n : ℕ} {m : Finset V → ℝ}
    (hm : IsWeight X n m) (he : (∅ : Finset V) ∈ X) (f : Finset V → ℝ) :
    ip X m 1 (fun σ => f σ - lowerWalk X m f σ) (fun _ => 1) = 0 := by
  have ha : ((∑ σ ∈ cells X 1, m σ * f σ) / m ∅) *
      ∑ σ ∈ cells X 1, m σ = ∑ σ ∈ cells X 1, m σ * f σ := by
    rw [vertex_mass hm he]
    exact div_mul_cancel₀ _ (hm.1 ∅ he).ne'
  unfold ip
  simp only [mul_one]
  have hh := weighted_center_zero (cells X 1) m f _ ha
  convert hh using 1
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [vertex_lowerWalk_mean X m f σ hσ he]

theorem vertex_center_contract {X : Finset (Finset V)} {n : ℕ} {m : Finset V → ℝ}
    (hm : IsWeight X n m) (he : (∅ : Finset V) ∈ X) (f : Finset V → ℝ) :
    ip X m 1 (fun σ => f σ - lowerWalk X m f σ)
      (fun σ => f σ - lowerWalk X m f σ) ≤ ip X m 1 f f := by
  have ha : ((∑ σ ∈ cells X 1, m σ * f σ) / m ∅) *
      ∑ σ ∈ cells X 1, m σ = ∑ σ ∈ cells X 1, m σ * f σ := by
    rw [vertex_mass hm he]
    exact div_mul_cancel₀ _ (hm.1 ∅ he).ne'
  have hh := weighted_center_contract (cells X 1) m f _
    (fun σ hσ => (hm.1 σ (mem_cells.mp hσ).1).le) ha
  convert hh using 1
  · unfold ip
    apply Finset.sum_congr rfl
    intro σ hσ
    dsimp only
    rw [vertex_lowerWalk_mean X m f σ hσ he]
    ring
  · unfold ip
    apply Finset.sum_congr rfl
    intro σ _
    ring

end HighOrderWalks.TwoSided.Fresh
end


section
noncomputable section
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh

lemma link_isPure {V : Type*} [DecidableEq V] {X : Finset (Finset V)} {n : ℕ}
    (hX : IsPureComplex X n) (η : Finset V) (hη : η ∈ X) (hc : η.card ≤ n) :
    IsPureComplex (link X η) (n - η.card) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro σ hσ τ hτσ
    have hs := mem_link.mp hσ
    apply mem_link.mpr
    refine ⟨hX.1 σ hs.1 τ hτσ, ?_, ?_⟩
    · exact hs.2.1.mono_right hτσ
    · exact hX.1 (η ∪ σ) hs.2.2 (η ∪ τ) (Finset.union_subset_union_right hτσ)
  · intro σ hσ
    have hbound := hX.2.1 (η ∪ σ) (mem_link.mp hσ).2.2
    have hsum := link_union_card hσ
    omega
  · intro σ hσ
    have hs := mem_link.mp hσ
    obtain ⟨ρ, hρ, hsub, hcard⟩ := hX.2.2.1 (η ∪ σ) hs.2.2
    have hηρ : η ⊆ ρ := fun _ hv => hsub (Finset.mem_union_left σ hv)
    have hσρ : σ ⊆ ρ := fun _ hv => hsub (Finset.mem_union_right η hv)
    refine ⟨ρ \ η, ?_, ?_, ?_⟩
    · apply mem_link.mpr
      refine ⟨hX.1 ρ hρ _ Finset.sdiff_subset, Finset.disjoint_sdiff, ?_⟩
      simpa only [Finset.union_sdiff_of_subset hηρ] using hρ
    · intro v hv
      apply Finset.mem_sdiff.mpr
      exact ⟨hσρ hv, fun hvη => Finset.disjoint_left.mp hs.2.1 hvη hv⟩
    · rw [Finset.card_sdiff_of_subset hηρ, hcard]
      omega
  · refine ⟨∅, mem_link.mpr ?_⟩
    refine ⟨hX.1 η hη ∅ (Finset.empty_subset _), ?_, ?_⟩
    · simp
    · simpa using hη

end HighOrderWalks.TwoSided.Fresh
end


section
noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh
variable {V : Type*} [DecidableEq V]

theorem vertex_center_pair {X : Finset (Finset V)} {m : Finset V → ℝ}
    (he : (∅ : Finset V) ∈ X) (f g : Finset V → ℝ)
    (hg : ip X m 1 g (fun _ => 1) = 0) :
    ip X m 1 g f = ip X m 1 g (fun σ => f σ - lowerWalk X m f σ) := by
  have hz : (∑ σ ∈ cells X 1, m σ * g σ) = 0 := by
    simpa only [ip, mul_one] using hg
  have hh : ip X m 1 g (fun σ => f σ - lowerWalk X m f σ) =
      ip X m 1 g f - (∑ σ ∈ cells X 1, m σ * g σ) *
        ((∑ σ ∈ cells X 1, m σ * f σ) / m ∅) := by
    unfold ip
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro σ hσ
    dsimp only
    rw [vertex_lowerWalk_mean X m f σ hσ he]
    ring
  rw [hh, hz, zero_mul, sub_zero]

theorem linkSummand_bound {X : Finset (Finset V)} {n k : ℕ} {m : Finset V → ℝ}
    {lam : ℝ} (hX : IsPureComplex X n) (hm : IsWeight X n m)
    (hlam : 0 ≤ lam) (hk : k + 1 ≤ n) (hL : LinkTwoSided X m k lam)
    {η : Finset V} (hη : η ∈ cells X k) (f : Finset V → ℝ) :
    |linkSummand X m η f f| ≤ lam * ip (link X η) (linkWeight m η) 1 (loc f η) (loc f η) := by
  have hc : η.card ≤ n := by rw [(mem_cells.mp hη).2]; omega
  have hlp := link_isPure hX η (mem_cells.mp hη).1 hc
  have hlw := link_isWeight hX hm hc
  have he : (∅ : Finset V) ∈ link X η := by
    apply mem_link.mpr
    exact ⟨hX.1 η (mem_cells.mp hη).1 _ (Finset.empty_subset _), by simp,
      by simpa using (mem_cells.mp hη).1⟩
  let g := fun σ => loc f η σ - lowerWalk (link X η) (linkWeight m η) (loc f η) σ
  have hg : ip (link X η) (linkWeight m η) 1 g (fun _ => 1) = 0 :=
    vertex_center_mean hlw he (loc f η)
  have hmg : ip (link X η) (linkWeight m η) 1
      (nonLazyWalk (link X η) (linkWeight m η) g) (fun _ => 1) = 0 := by
    rw [nonLazy_mean hlp hlw (by rw [(mem_cells.mp hη).2]; omega) (by omega), hg]
  unfold linkSummand
  change |ip (link X η) (linkWeight m η) 1
    (nonLazyWalk (link X η) (linkWeight m η) g) (loc f η)| ≤ _
  rw [vertex_center_pair he (loc f η) _ hmg]
  exact (hL η hη g hg).trans (mul_le_mul_of_nonneg_left
    (vertex_center_contract hlw he (loc f η)) hlam)

theorem linkTerm_bound {X : Finset (Finset V)} {n k : ℕ} {m : Finset V → ℝ}
    {lam : ℝ} (hX : IsPureComplex X n) (hm : IsWeight X n m)
    (hlam : 0 ≤ lam) (hk : k + 1 ≤ n) (hL : LinkTwoSided X m k lam)
    (f : Finset V → ℝ) :
    |linkTerm X m k f f| ≤ (k + 1 : ℝ) * lam * ip X m (k + 1) f f := by
  unfold linkTerm
  calc
    _ ≤ ∑ η ∈ cells X k, |linkSummand X m η f f| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ η ∈ cells X k, lam * ip (link X η) (linkWeight m η) 1 (loc f η) (loc f η) :=
      Finset.sum_le_sum (fun η hη => linkSummand_bound hX hm hlam hk hL hη f)
    _ = _ := by
      rw [← Finset.mul_sum, localization_ip_sum hX m k f f]
      ring

end HighOrderWalks.TwoSided.Fresh
end


section
noncomputable section
open scoped BigOperators
open HighOrderWalks.OneSided
namespace HighOrderWalks.TwoSided.Fresh

lemma sum_supported_pair {α : Type*} [DecidableEq α] (s : Finset α)
    (a b : α) (hab : a ≠ b) (ha : a ∈ s) (hb : b ∈ s)
    (f : α → ℝ) (hf : ∀ x ∈ s, x ≠ a → x ≠ b → f x = 0) :
    ∑ x ∈ s, f x = f a + f b := by
  have hsub : ({a, b} : Finset α) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hsum := Finset.sum_subset hsub (fun x hx hn =>
    hf x hx (by intro h; subst x; simp at hn)
      (by intro h; subst x; simp at hn))
  simpa [hab] using hsum.symm

lemma expansion_parameter_nonneg {V : Type*} [DecidableEq V]
    (X : Finset (Finset V)) (n : ℕ) (hX : IsPureComplex X n)
    (m : Finset V → ℝ) (hm : IsWeight X n m) (lam : ℝ)
    (hexp : TwoSidedLSE X m n lam) (hn : 1 ≤ n) : 0 ≤ lam := by
  obtain ⟨σ, hσ⟩ := hX.2.2.2
  obtain ⟨ρ, hρ, _, hcard⟩ := hX.2.2.1 σ hσ
  have htwo : 1 < ρ.card := by omega
  obtain ⟨u, huρ, v, hvρ, huv⟩ := Finset.one_lt_card.mp htwo
  have hu : ({u} : Finset V) ∈ X := hX.1 ρ hρ _ (Finset.singleton_subset_iff.mpr huρ)
  have hv : ({v} : Finset V) ∈ X := hX.1 ρ hρ _ (Finset.singleton_subset_iff.mpr hvρ)
  have huv' : ({u} : Finset V) ≠ {v} := by simpa using huv
  have huc : ({u} : Finset V) ∈ cells X 1 := mem_cells.mpr ⟨hu, by simp⟩
  have hvc : ({v} : Finset V) ∈ cells X 1 := mem_cells.mpr ⟨hv, by simp⟩
  have hempty : (∅ : Finset V) ∈ cells X 0 :=
    mem_cells.mpr ⟨hX.1 ρ hρ _ (Finset.empty_subset _), by simp⟩
  have hlink : link X (∅ : Finset V) = X := by
    ext τ
    simp [link]
  have hweight : linkWeight m (∅ : Finset V) = m := by
    funext τ
    simp [linkWeight]
  let g : Finset V → ℝ := fun τ => if τ = {u} then m {v} else if τ = {v} then -m {u} else 0
  have hgu : g {u} = m {v} := by simp [g]
  have hgv : g {v} = -m {u} := by simp [g, huv'.symm]
  have hgz : ∀ τ, τ ≠ {u} → τ ≠ {v} → g τ = 0 := by
    intro τ hτu hτv
    simp [g, hτu, hτv]
  have hmean : ip X m 1 g (fun _ => 1) = 0 := by
    unfold ip
    rw [sum_supported_pair (cells X 1) {u} {v} huv' huc hvc
      (fun τ => m τ * g τ * 1) (by
        intro τ _ hτu hτv
        simp [hgz τ hτu hτv])]
    rw [hgu, hgv]
    ring
  have hnorm : ip X m 1 g g = m {u} * m {v} * m {v} +
      m {v} * (-m {u}) * (-m {u}) := by
    unfold ip
    rw [sum_supported_pair (cells X 1) {u} {v} huv' huc hvc
      (fun τ => m τ * g τ * g τ) (by
        intro τ _ hτu hτv
        simp [hgz τ hτu hτv])]
    rw [hgu, hgv]
  have hmu : 0 < m {u} := hm.1 _ hu
  have hmv : 0 < m {v} := hm.1 _ hv
  have hpos : 0 < ip X m 1 g g := by
    rw [hnorm]
    have hp : 0 < m {u} * m {v} * m {v} := by positivity
    have hq : 0 ≤ m {v} * (-m {u}) * (-m {u}) := by
      have hh := mul_nonneg (le_of_lt hmv) (sq_nonneg (m {u}))
      nlinarith
    linarith
  have hlocal := hexp 0 hn ∅ hempty g
  rw [hlink, hweight] at hlocal
  have h := hlocal hmean
  have hprod : 0 ≤ lam * ip X m 1 g g := le_trans (abs_nonneg _) h
  exact nonneg_of_mul_nonneg_left hprod hpos

end HighOrderWalks.TwoSided.Fresh
end


/- Supporting lemmas from Nickrobbins95, accepted Prove2Me submission f3347acc-2e62-4054-8da8-fa7228623546. -/

set_option autoImplicit false

namespace HOW54

open HighOrderWalks.OneSided Finset

variable {V : Type*} [DecidableEq V]

/-- faces one vertex above `σ` -/
def U (X : Finset (Finset V)) (σ : Finset V) : Finset (Finset V) :=
  X.filter (fun ρ => ρ.card = σ.card + 1 ∧ σ ⊆ ρ)

/-- faces one vertex below `ρ` -/
def D (X : Finset (Finset V)) (ρ : Finset V) : Finset (Finset V) :=
  X.filter (fun τ => τ ⊆ ρ ∧ τ.card + 1 = ρ.card)

/-- upper neighbours of `σ` -/
def W (X : Finset (Finset V)) (σ : Finset V) : Finset (Finset V) :=
  X.filter (fun σ' => σ'.card = σ.card ∧ σ' ≠ σ ∧ σ ∪ σ' ∈ X ∧ (σ ∪ σ').card = σ.card + 1)

theorem exch (X : Finset (Finset V)) (k : ℕ) (F : Finset V → Finset V → ℝ) :
    ∑ τ ∈ cells X k, ∑ σ ∈ U X τ, F τ σ = ∑ σ ∈ cells X (k + 1), ∑ τ ∈ D X σ, F τ σ := by
  apply Finset.sum_comm'
  intro τ σ
  simp only [cells, U, D, mem_filter]
  constructor
  · rintro ⟨⟨hτ, hk⟩, hσ, hc, hsub⟩
    exact ⟨⟨hτ, hsub, by omega⟩, hσ, by omega⟩
  · rintro ⟨⟨hτ, hsub, hc⟩, hσ, hk⟩
    exact ⟨⟨hτ, by omega⟩, hσ, by omega, hsub⟩

theorem card_D {X : Finset (Finset V)} (hdc : ∀ σ ∈ X, ∀ τ, τ ⊆ σ → τ ∈ X) {σ : Finset V}
    (hσ : σ ∈ X) {k : ℕ} (hk : σ.card = k + 1) : (D X σ).card = k + 1 := by
  have : D X σ = σ.powersetCard k := by
    ext τ
    simp only [D, mem_filter, mem_powersetCard]
    constructor
    · rintro ⟨-, h1, h2⟩
      exact ⟨h1, by omega⟩
    · rintro ⟨h1, h2⟩
      exact ⟨hdc σ hσ τ h1, h1, by omega⟩
  rw [this, card_powersetCard, hk, Nat.choose_succ_self_right]

theorem sumU {X : Finset (Finset V)} (hdc : ∀ σ ∈ X, ∀ τ, τ ⊆ σ → τ ∈ X) (k : ℕ)
    (F : Finset V → ℝ) :
    ∑ τ ∈ cells X k, ∑ σ ∈ U X τ, F σ = ((k : ℝ) + 1) * ∑ σ ∈ cells X (k + 1), F σ := by
  rw [exch X k (fun _ σ => F σ), mul_sum]
  apply sum_congr rfl
  intro σ hσ
  simp only [cells, mem_filter] at hσ
  rw [sum_const, card_D hdc hσ.1 hσ.2, nsmul_eq_mul]
  push_cast
  ring

theorem union_eq {σ σ' ρ : Finset V} (h1 : σ ⊆ ρ) (h2 : σ' ⊆ ρ) (hc : σ'.card = σ.card)
    (hne : σ' ≠ σ) (hρ : ρ.card = σ.card + 1) : σ ∪ σ' = ρ := by
  apply Finset.eq_of_subset_of_card_le (Finset.union_subset h1 h2)
  rw [hρ]
  have hss : σ ⊂ σ ∪ σ' := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left, ?_⟩
    intro heq
    apply hne
    have : σ' ⊆ σ := by
      calc σ' ⊆ σ ∪ σ' := Finset.subset_union_right
        _ = σ := heq.symm
    exact Finset.eq_of_subset_of_card_le this (by omega)
  have := Finset.card_lt_card hss
  omega

theorem key1a {X : Finset (Finset V)} {n : ℕ} (hX : IsPureComplex X n) {m : Finset V → ℝ}
    (hm : IsWeight X n m) {k : ℕ} (hk : k + 1 ≤ n) (φ ψ : Finset V → ℝ) :
    ip X m (k + 1 + 1) (dS X φ) (dS X ψ) =
      ∑ σ ∈ cells X (k + 1), m σ * φ σ * ψ σ +
        ∑ σ ∈ cells X (k + 1), ∑ σ' ∈ W X σ, m (σ ∪ σ') * φ σ' * ψ σ := by
  have hL : ip X m (k + 1 + 1) (dS X φ) (dS X ψ) =
      ∑ ρ ∈ cells X (k + 1 + 1), ∑ σ ∈ D X ρ, (m ρ * φ σ * ψ σ +
        ∑ σ' ∈ (D X ρ).erase σ, m ρ * φ σ' * ψ σ) := by
    unfold ip
    apply sum_congr rfl
    intro ρ hρ
    have hρX : ρ ∈ X := (mem_filter.mp hρ).1
    have e1 : dS X φ ρ = ∑ τ ∈ D X ρ, φ τ := by simp only [dS, if_pos hρX, D]
    have e2 : dS X ψ ρ = ∑ τ ∈ D X ρ, ψ τ := by simp only [dS, if_pos hρX, D]
    have : ∀ σ ∈ D X ρ, m ρ * φ σ * ψ σ + ∑ σ' ∈ (D X ρ).erase σ, m ρ * φ σ' * ψ σ
        = (m ρ * ∑ τ ∈ D X ρ, φ τ) * ψ σ := by
      intro σ hσ
      rw [Finset.add_sum_erase _ (fun σ' => m ρ * φ σ' * ψ σ) hσ, Finset.mul_sum, Finset.sum_mul]
    rw [sum_congr rfl this, ← Finset.mul_sum, e1, e2]
  rw [hL, ← exch X (k + 1), ← sum_add_distrib]
  apply sum_congr rfl
  intro σ hσ
  have hσ' := mem_filter.mp hσ
  rw [sum_add_distrib]
  congr 1
  · have hw : ∑ ρ ∈ U X σ, m ρ = m σ := (hm.2 σ hσ'.1 (by omega)).symm
    rw [← sum_mul, ← sum_mul, hw]
  · rw [Finset.sum_comm' (t' := W X σ) (s' := fun σ' => {σ ∪ σ'})]
    · simp only [sum_singleton]
    · intro ρ σ'
      simp only [U, D, W, mem_filter, mem_erase, mem_singleton]
      constructor
      · rintro ⟨⟨hρX, hρc, hσρ⟩, hne, hσ'X, hσ'ρ, hσ'c⟩
        have hu := union_eq hσρ hσ'ρ (by omega) hne hρc
        refine ⟨hu.symm, hσ'X, by omega, hne, by rw [hu]; exact hρX, by rw [hu]; exact hρc⟩
      · rintro ⟨rfl, hσ'X, hc, hne, hu, huc⟩
        exact ⟨⟨hu, huc, subset_union_left⟩, hne, hσ'X, subset_union_right, by omega⟩

theorem key1b {X : Finset (Finset V)} {n : ℕ} {m : Finset V → ℝ}
    (hm : IsWeight X n m) {k : ℕ} (φ ψ : Finset V → ℝ) :
    ((k : ℝ) + 1 + 1) * ip X m (k + 1) (upperWalk X m φ) ψ =
      ∑ σ ∈ cells X (k + 1), m σ * φ σ * ψ σ +
        ∑ σ ∈ cells X (k + 1), ∑ σ' ∈ W X σ, m (σ ∪ σ') * φ σ' * ψ σ := by
  unfold ip
  rw [mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro σ hσ
  simp only [cells, mem_filter] at hσ
  obtain ⟨hσX, hσc⟩ := hσ
  have hmσ : m σ ≠ 0 := (hm.1 σ hσX).ne'
  have hc : ((σ.card : ℕ) : ℝ) + 1 = (k : ℝ) + 1 + 1 := by rw [hσc]; push_cast; ring
  have h2 : (k : ℝ) + 1 + 1 ≠ 0 := by positivity
  have hu : upperWalk X m φ σ = φ σ / ((k : ℝ) + 1 + 1) +
      ∑ σ' ∈ W X σ, m (σ ∪ σ') / (((k : ℝ) + 1 + 1) * m σ) * φ σ' := by
    simp only [upperWalk, if_pos hσX, hc, W]
  have hs : ∑ σ' ∈ W X σ, m (σ ∪ σ') / (((k : ℝ) + 1 + 1) * m σ) * φ σ' =
      (∑ σ' ∈ W X σ, m (σ ∪ σ') * φ σ') / (((k : ℝ) + 1 + 1) * m σ) := by
    rw [Finset.sum_div]
    apply sum_congr rfl
    intro σ' _
    ring
  rw [hu, hs, ← Finset.sum_mul]
  first
    | (field_simp; ring)
    | field_simp

theorem B1 {X : Finset (Finset V)} (hdc : ∀ σ ∈ X, ∀ τ, τ ⊆ σ → τ ∈ X) {τ : Finset V}
    (F : Finset V → ℝ) :
    ∑ η ∈ cells (link X τ) 1, F (τ ∪ η) = ∑ σ ∈ U X τ, F σ := by
  apply Finset.sum_nbij' (fun η => τ ∪ η) (fun σ => σ \ τ)
  · intro η hη
    simp only [cells, link, U, mem_filter] at hη ⊢
    obtain ⟨⟨-, hd, hu⟩, h1⟩ := hη
    exact ⟨hu, by rw [card_union_eq_card_add_card.mpr hd, h1], subset_union_left⟩
  · intro σ hσ
    simp only [cells, link, U, mem_filter] at hσ ⊢
    obtain ⟨hσX, hc, hsub⟩ := hσ
    refine ⟨⟨hdc σ hσX _ sdiff_subset, disjoint_sdiff, ?_⟩, ?_⟩
    · rw [union_sdiff_of_subset hsub]; exact hσX
    · have := card_sdiff_add_card_eq_card hsub; omega
  · intro η hη
    simp only [cells, link, mem_filter] at hη
    exact union_sdiff_cancel_left hη.1.2.1
  · intro σ hσ
    simp only [U, mem_filter] at hσ
    exact union_sdiff_of_subset hσ.2.2
  · intro η _
    rfl

theorem B2 {X : Finset (Finset V)} (hdc : ∀ σ ∈ X, ∀ τ, τ ⊆ σ → τ ∈ X) {τ η : Finset V}
    (hη : η ∈ cells (link X τ) 1) (F : Finset V → ℝ) :
    ∑ η' ∈ W (link X τ) η, F (τ ∪ η') =
      ∑ σ' ∈ (W X (τ ∪ η)).filter (fun σ' => τ ⊆ σ'), F σ' := by
  simp only [cells, link, mem_filter] at hη
  obtain ⟨⟨hηX, hdη, huη⟩, hη1⟩ := hη
  have hcη : (τ ∪ η).card = τ.card + 1 := by rw [card_union_eq_card_add_card.mpr hdη, hη1]
  apply Finset.sum_nbij' (fun η' => τ ∪ η') (fun σ' => σ' \ τ)
  · intro η' h
    simp only [W, link, mem_filter] at h ⊢
    obtain ⟨⟨hη'X, hd', hu'⟩, hc', hne, ⟨hUX, hdU, huU⟩, hcU⟩ := h
    have e : τ ∪ η ∪ (τ ∪ η') = τ ∪ (η ∪ η') := by
      ext x; simp only [mem_union]; tauto
    refine ⟨⟨hu', ?_, ?_, ?_, ?_⟩, subset_union_left⟩
    · rw [card_union_eq_card_add_card.mpr hd']; omega
    · intro h; apply hne
      have h' : (τ ∪ η') \ τ = (τ ∪ η) \ τ := by rw [h]
      rwa [union_sdiff_cancel_left hd', union_sdiff_cancel_left hdη] at h'
    · rw [e]; exact huU
    · rw [e, card_union_eq_card_add_card.mpr hdU]; omega
  · intro σ' h
    simp only [W, link, mem_filter] at h ⊢
    obtain ⟨⟨hσ'X, hc', hne, hUX, hcU⟩, hsub⟩ := h
    have e1 : τ ∪ (σ' \ τ) = σ' := union_sdiff_of_subset hsub
    have e2 : τ ∪ (η ∪ σ' \ τ) = τ ∪ η ∪ σ' := by
      ext x; simp only [mem_union, mem_sdiff]; have := @hsub x; tauto
    have hdA : Disjoint τ (η ∪ σ' \ τ) := disjoint_union_right.mpr ⟨hdη, disjoint_sdiff⟩
    have hcs : (σ' \ τ).card + τ.card = σ'.card := card_sdiff_add_card_eq_card hsub
    refine ⟨⟨hdc σ' hσ'X _ sdiff_subset, disjoint_sdiff, by rw [e1]; exact hσ'X⟩, by omega, ?_,
      ⟨?_, hdA, by rw [e2]; exact hUX⟩, ?_⟩
    · intro h; apply hne; rw [← e1, h]
    · exact hdc _ hUX _ (by rw [← e2]; exact subset_union_right)
    · have := card_union_eq_card_add_card.mpr hdA
      rw [e2, hcU, hcη] at this
      omega
  · intro η' h
    simp only [W, link, mem_filter] at h
    exact union_sdiff_cancel_left h.1.2.1
  · intro σ' h
    simp only [mem_filter] at h
    exact union_sdiff_of_subset h.2
  · intro _ _
    rfl

theorem link1 {X : Finset (Finset V)} (hdc : ∀ σ ∈ X, ∀ τ, τ ⊆ σ → τ ∈ X)
    {m : Finset V → ℝ} (hpos : ∀ σ ∈ X, 0 < m σ) {τ : Finset V} (f : Finset V → ℝ) :
    ip (link X τ) (linkWeight m τ) 1 (nonLazyWalk (link X τ) (linkWeight m τ) (loc f τ))
        (loc f τ) =
      ∑ σ ∈ U X τ, ∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), m (σ ∪ σ') * f σ' * f σ := by
  unfold ip
  rw [← B1 hdc (fun σ => ∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), m (σ ∪ σ') * f σ' * f σ)]
  apply sum_congr rfl
  intro η hη
  have hη' := hη
  simp only [cells, link, mem_filter] at hη'
  obtain ⟨⟨hηX, hdη, huη⟩, hη1⟩ := hη'
  have hηL : η ∈ link X τ := mem_filter.mpr ⟨hηX, hdη, huη⟩
  have hw : linkWeight m τ η ≠ 0 := (hpos _ huη).ne'
  have hc : ((η.card : ℕ) : ℝ) = 1 := by rw [hη1]; norm_num
  rw [← B2 hdc hη (fun σ' => m (τ ∪ η ∪ σ') * f σ' * f (τ ∪ η))]
  have e : ∀ η' ∈ W (link X τ) η, m (τ ∪ η ∪ (τ ∪ η')) = linkWeight m τ (η ∪ η') := by
    intro η' _
    simp only [linkWeight]
    congr 1
    ext x; simp only [mem_union]; tauto
  have e' : ∑ η' ∈ W (link X τ) η, m (τ ∪ η ∪ (τ ∪ η')) * f (τ ∪ η') * f (τ ∪ η) =
      ∑ η' ∈ W (link X τ) η, linkWeight m τ (η ∪ η') * loc f τ η' * loc f τ η :=
    sum_congr rfl (fun η' h => by simp only [e η' h, loc])
  rw [e']
  simp only [nonLazyWalk, upperWalk, if_pos hηL, hc, W, div_mul_eq_mul_div, ← Finset.sum_div,
    ← Finset.sum_mul]
  first
    | (field_simp; ring)
    | field_simp

theorem inter_eq {X : Finset (Finset V)} {τ σ σ' : Finset V} (hσ : σ ∈ U X τ)
    (hσ' : σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ')) : σ ∩ σ' = τ := by
  simp only [U, W, mem_filter] at hσ hσ'
  obtain ⟨hσX, hσc, hτσ⟩ := hσ
  obtain ⟨⟨hX', hc', hne, hu, huc⟩, hτσ'⟩ := hσ'
  have := card_union_add_card_inter σ σ'
  exact (Finset.eq_of_subset_of_card_le (subset_inter hτσ hτσ') (by omega)).symm

theorem R1 {X : Finset (Finset V)} (hdc : ∀ σ ∈ X, ∀ τ, τ ⊆ σ → τ ∈ X) {n : ℕ}
    {m : Finset V → ℝ} (hm : IsWeight X n m) {τ σ : Finset V} (hσ : σ ∈ U X τ)
    (hn : σ.card ≤ n) :
    ∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), m (σ ∪ σ') = m σ := by
  have hσ0 := hσ
  simp only [U, mem_filter] at hσ0
  obtain ⟨hσX, hσc, hτσ⟩ := hσ0
  have hw : m σ = ∑ ρ ∈ U X σ, m ρ := hm.2 σ hσX hn
  rw [hw]
  have hcd : (σ \ τ).card = 1 := by have := card_sdiff_add_card_eq_card hτσ; omega
  apply Finset.sum_nbij' (fun σ' => σ ∪ σ') (fun ρ => ρ \ (σ \ τ))
  · intro σ' h
    have h0 := h
    simp only [W, mem_filter] at h0
    simp only [U, mem_filter]
    exact ⟨h0.1.2.2.2.1, h0.1.2.2.2.2, subset_union_left⟩
  · intro ρ h
    simp only [U, mem_filter] at h
    obtain ⟨hρX, hρc, hσρ⟩ := h
    have e : σ ∪ ρ \ (σ \ τ) = ρ := by
      ext x; simp only [mem_union, mem_sdiff]; have := @hσρ x; tauto
    have hsub : σ \ τ ⊆ ρ := sdiff_subset.trans hσρ
    have hc2 := card_sdiff_add_card_eq_card hsub
    simp only [W, mem_filter]
    refine ⟨⟨hdc ρ hρX _ sdiff_subset, by omega, ?_, by rw [e]; exact hρX, by rw [e]; exact hρc⟩, ?_⟩
    · intro h
      obtain ⟨x, hx⟩ := card_pos.mp (by omega : 0 < (σ \ τ).card)
      have hxσ : x ∈ σ := (mem_sdiff.mp hx).1
      rw [← h] at hxσ
      exact (mem_sdiff.mp hxσ).2 hx
    · intro x hx
      exact mem_sdiff.mpr ⟨hσρ (hτσ hx), fun h => (mem_sdiff.mp h).2 hx⟩
  · intro σ' h
    have hi := inter_eq hσ h
    have h0 := h
    simp only [mem_filter] at h0
    ext x
    simp only [mem_union, mem_sdiff]
    constructor
    · rintro ⟨hx | hx, hnx⟩
      · by_cases hxτ : x ∈ τ
        · exact h0.2 hxτ
        · exact absurd ⟨hx, hxτ⟩ hnx
      · exact hx
    · intro hx
      refine ⟨Or.inr hx, ?_⟩
      rintro ⟨hxσ, hxτ⟩
      apply hxτ
      rw [← hi]
      exact mem_inter.mpr ⟨hxσ, hx⟩
  · intro ρ h
    simp only [U, mem_filter] at h
    have hs2 := h.2.2
    ext x; simp only [mem_union, mem_sdiff]; have := @hs2 x; tauto
  · intro _ _
    rfl

theorem SYM {X : Finset (Finset V)} {τ : Finset V} (H : Finset V → Finset V → ℝ) :
    ∑ σ ∈ U X τ, ∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), H σ σ' =
      ∑ σ ∈ U X τ, ∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), H σ' σ := by
  rw [Finset.sum_comm' (t' := U X τ) (s' := fun σ' => (W X σ').filter (fun σ => τ ⊆ σ))]
  intro σ σ'
  simp only [U, W, mem_filter]
  constructor
  · rintro ⟨⟨hX, hc, hτ⟩, ⟨hX', hc', hne, hu, huc⟩, hτ'⟩
    exact ⟨⟨⟨hX, by omega, fun h => hne h.symm, by rw [union_comm]; exact hu,
      by rw [union_comm]; omega⟩, hτ⟩, hX', by omega, hτ'⟩
  · rintro ⟨⟨⟨hX, hc, hne, hu, huc⟩, hτ⟩, hX', hc', hτ'⟩
    exact ⟨⟨hX, by omega, hτ⟩, ⟨hX', by omega, fun h => hne h.symm, by rw [union_comm]; exact hu,
      by rw [union_comm]; omega⟩, hτ'⟩

theorem G2 {X : Finset (Finset V)} (hdc : ∀ σ ∈ X, ∀ τ, τ ⊆ σ → τ ∈ X) (k : ℕ)
    (G : Finset V → Finset V → ℝ) :
    ∑ τ ∈ cells X k, ∑ σ ∈ U X τ, ∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), G σ σ' =
      ∑ σ ∈ cells X (k + 1), ∑ σ' ∈ W X σ, G σ σ' := by
  rw [exch X k]
  apply sum_congr rfl
  intro σ hσ
  have hσX : σ ∈ X := (mem_filter.mp hσ).1
  rw [Finset.sum_comm' (t' := W X σ) (s' := fun σ' => (D X σ).filter (fun τ => τ ⊆ σ'))]
  · apply sum_congr rfl
    intro σ' hσ'
    have hs : (D X σ).filter (fun τ => τ ⊆ σ') = {σ ∩ σ'} := by
      have h0 := hσ'
      simp only [W, mem_filter] at h0
      obtain ⟨hX', hc', hne, hu, huc⟩ := h0
      have hcu := card_union_add_card_inter σ σ'
      ext τ
      simp only [D, mem_filter, mem_singleton]
      constructor
      · rintro ⟨⟨hτX, hτσ, hτc⟩, hτσ'⟩
        exact Finset.eq_of_subset_of_card_le (subset_inter hτσ hτσ') (by omega)
      · rintro rfl
        exact ⟨⟨hdc σ hσX _ inter_subset_left, inter_subset_left, by omega⟩, inter_subset_right⟩
    rw [hs, sum_singleton]
  · intro τ σ'
    simp only [mem_filter]
    tauto

theorem ip_nonneg {X : Finset (Finset V)} {m : Finset V → ℝ} (hpos : ∀ σ ∈ X, 0 < m σ)
    (c : ℕ) (f : Finset V → ℝ) : 0 ≤ ip X m c f f := by
  unfold ip
  apply sum_nonneg
  intro σ hσ
  have := hpos σ (mem_filter.mp hσ).1
  rw [mul_assoc]
  exact mul_nonneg this.le (mul_self_nonneg _)

theorem ip_cs {X : Finset (Finset V)} {m : Finset V → ℝ} (hpos : ∀ σ ∈ X, 0 < m σ)
    (c : ℕ) (f g : Finset V → ℝ) :
    (ip X m c f g) ^ 2 ≤ ip X m c f f * ip X m c g g := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (cells X c) (fun σ => Real.sqrt (m σ) * f σ)
    (fun σ => Real.sqrt (m σ) * g σ)
  have hm' : ∀ σ ∈ cells X c, Real.sqrt (m σ) ^ 2 = m σ :=
    fun σ hσ => Real.sq_sqrt (hpos σ (mem_filter.mp hσ).1).le
  have e1 : ∑ σ ∈ cells X c, Real.sqrt (m σ) * f σ * (Real.sqrt (m σ) * g σ) = ip X m c f g := by
    unfold ip; apply sum_congr rfl; intro σ hσ
    rw [show Real.sqrt (m σ) * f σ * (Real.sqrt (m σ) * g σ) = Real.sqrt (m σ) ^ 2 * f σ * g σ by
      ring, hm' σ hσ]
  have e2 : ∑ σ ∈ cells X c, (Real.sqrt (m σ) * f σ) ^ 2 = ip X m c f f := by
    unfold ip; apply sum_congr rfl; intro σ hσ
    rw [mul_pow, hm' σ hσ]; ring
  have e3 : ∑ σ ∈ cells X c, (Real.sqrt (m σ) * g σ) ^ 2 = ip X m c g g := by
    unfold ip; apply sum_congr rfl; intro σ hσ
    rw [mul_pow, hm' σ hσ]; ring
  calc (ip X m c f g) ^ 2
      = (∑ σ ∈ cells X c, Real.sqrt (m σ) * f σ * (Real.sqrt (m σ) * g σ)) ^ 2 := by rw [e1]
    _ ≤ (∑ σ ∈ cells X c, (Real.sqrt (m σ) * f σ) ^ 2) *
          ∑ σ ∈ cells X c, (Real.sqrt (m σ) * g σ) ^ 2 := h
    _ = ip X m c f f * ip X m c g g := by rw [e2, e3]

theorem ADJ (X : Finset (Finset V)) (m : Finset V → ℝ) (k : ℕ) (φ ψ : Finset V → ℝ) :
    ∑ σ ∈ cells X (k + 1), m σ * φ σ * dS X ψ σ =
      ∑ τ ∈ cells X k, ψ τ * ∑ σ ∈ U X τ, m σ * φ σ := by
  simp only [Finset.mul_sum]
  rw [exch X k]
  apply sum_congr rfl
  intro σ hσ
  have hσX : σ ∈ X := (mem_filter.mp hσ).1
  simp only [dS, if_pos hσX, Finset.mul_sum, D]
  apply sum_congr rfl
  intro τ _
  ring

theorem local_ineq {X : Finset (Finset V)} {n : ℕ} (hX : IsPureComplex X n) {m : Finset V → ℝ}
    (hm : IsWeight X n m) {lam : ℝ} {k : ℕ} (hk : k + 1 ≤ n)
    (hlink : LinkUpper X m k lam) {τ : Finset V} (hτ : τ ∈ cells X k) (φ : Finset V → ℝ) :
    ∑ σ ∈ U X τ, ∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), m (σ ∪ σ') * φ σ' * φ σ ≤
      lam * ∑ σ ∈ U X τ, m σ * φ σ * φ σ +
        (1 - lam) * ((∑ σ ∈ U X τ, m σ * φ σ) ^ 2 / m τ) := by
  have hdc := hX.1
  have hpos := hm.1
  have hτ0 := mem_filter.mp hτ
  have hτX : τ ∈ X := hτ0.1
  have hτc : τ.card = k := hτ0.2
  have hmτ : 0 < m τ := hpos τ hτX
  have hwτ : ∑ σ ∈ U X τ, m σ = m τ := (hm.2 τ hτX (by omega)).symm
  have hσn : ∀ σ ∈ U X τ, σ.card ≤ n := by
    intro σ hσ
    have := (mem_filter.mp hσ).2.1
    omega
  have hR1 : ∀ σ ∈ U X τ, ∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), m (σ ∪ σ') = m σ :=
    fun σ hσ => R1 hdc hm hσ (hσn σ hσ)
  obtain ⟨A, hA⟩ : ∃ A, ∑ σ ∈ U X τ, m σ * φ σ = A := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, a = A / m τ := ⟨_, rfl⟩
  have hamτ : a * m τ = A := by rw [ha, div_mul_cancel₀ A hmτ.ne']
  rw [hA]
  have horth : ip (link X τ) (linkWeight m τ) 1 (loc (fun σ => φ σ - a) τ) (fun _ => 1) = 0 := by
    have e : ip (link X τ) (linkWeight m τ) 1 (loc (fun σ => φ σ - a) τ) (fun _ => 1) =
        ∑ σ ∈ U X τ, m σ * (φ σ - a) * 1 := B1 hdc (fun σ => m σ * (φ σ - a) * 1)
    rw [e]
    have : ∀ σ ∈ U X τ, m σ * (φ σ - a) * 1 = m σ * φ σ - a * m σ := fun _ _ => by ring
    rw [sum_congr rfl this, sum_sub_distrib, ← mul_sum, hA, hwτ, hamτ, sub_self]
  have hle := hlink τ hτ (loc (fun σ => φ σ - a) τ) horth
  rw [link1 hdc hpos (fun σ => φ σ - a)] at hle
  have e2 : ip (link X τ) (linkWeight m τ) 1 (loc (fun σ => φ σ - a) τ)
      (loc (fun σ => φ σ - a) τ) = ∑ σ ∈ U X τ, m σ * (φ σ - a) * (φ σ - a) :=
    B1 hdc (fun σ => m σ * (φ σ - a) * (φ σ - a))
  rw [e2] at hle
  have hC : ∑ σ ∈ U X τ, ∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), m (σ ∪ σ') * φ σ' = A := by
    rw [SYM (fun σ σ' => m (σ ∪ σ') * φ σ'), ← hA]
    apply sum_congr rfl
    intro σ hσ
    rw [← sum_mul, ← hR1 σ hσ]
    congr 1
    apply sum_congr rfl
    intro σ' _
    rw [union_comm]
  have hL : ∑ σ ∈ U X τ, ∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'),
        m (σ ∪ σ') * (φ σ' - a) * (φ σ - a) =
      (∑ σ ∈ U X τ, ∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), m (σ ∪ σ') * φ σ' * φ σ)
        - a * A - a * A + a ^ 2 * m τ := by
    calc ∑ σ ∈ U X τ, ∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'),
          m (σ ∪ σ') * (φ σ' - a) * (φ σ - a)
        = ∑ σ ∈ U X τ, (∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), m (σ ∪ σ') * φ σ' * φ σ
            - a * ∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), m (σ ∪ σ') * φ σ'
            - a * φ σ * ∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), m (σ ∪ σ')
            + a ^ 2 * ∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), m (σ ∪ σ')) := by
          apply sum_congr rfl
          intro σ _
          simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
          apply sum_congr rfl
          intro σ' _
          ring
      _ = ∑ σ ∈ U X τ, (∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), m (σ ∪ σ') * φ σ' * φ σ
            - a * ∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), m (σ ∪ σ') * φ σ'
            - a * (m σ * φ σ) + a ^ 2 * m σ) := by
          apply sum_congr rfl
          intro σ hσ
          rw [hR1 σ hσ]
          ring
      _ = _ := by
          rw [sum_add_distrib, sum_sub_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, ← mul_sum,
            hC, hA, hwτ]
  have hS : ∑ σ ∈ U X τ, m σ * (φ σ - a) * (φ σ - a) =
      (∑ σ ∈ U X τ, m σ * φ σ * φ σ) - a * A - a * A + a ^ 2 * m τ := by
    have : ∀ σ ∈ U X τ, m σ * (φ σ - a) * (φ σ - a) =
        m σ * φ σ * φ σ - a * (m σ * φ σ) - a * (m σ * φ σ) + a ^ 2 * m σ := fun _ _ => by ring
    rw [sum_congr rfl this, sum_add_distrib, sum_sub_distrib, sum_sub_distrib, ← mul_sum,
      ← mul_sum, hA, hwτ]
  rw [hL, hS] at hle
  have e1 : A ^ 2 / m τ = a * A := by
    rw [← hamτ]
    first
      | (field_simp; ring)
      | field_simp
  have e3 : a ^ 2 * m τ = a * A := by rw [← hamτ]; ring
  have e4 : lam * (a ^ 2 * m τ) = lam * (a * A) := by rw [e3]
  rw [e1]
  nlinarith [hle, e3, e4]

theorem step {X : Finset (Finset V)} {n : ℕ} (hX : IsPureComplex X n) {m : Finset V → ℝ}
    (hm : IsWeight X n m) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hexp : OneSidedLSE X m n lam) {k : ℕ} (hk : k + 1 ≤ n) (φ : Finset V → ℝ) (C : ℝ)
    (hB : ∑ τ ∈ cells X k, (∑ σ ∈ U X τ, m σ * φ σ) ^ 2 / m τ ≤ C * ip X m (k + 1) φ φ) :
    ip X m (k + 1 + 1) (dS X φ) (dS X φ) ≤
      (1 + lam * ((k : ℝ) + 1) + C) * ip X m (k + 1) φ φ := by
  have hdc := hX.1
  have hE := key1a hX hm hk φ φ
  rw [← G2 hdc k (fun σ σ' => m (σ ∪ σ') * φ σ' * φ σ)] at hE
  have hT := sum_le_sum (fun τ (hτ : τ ∈ cells X k) => local_ineq hX hm hk (hexp k hk) hτ φ)
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, sumU hdc k (fun σ => m σ * φ σ * φ σ)] at hT
  have hB0 : 0 ≤ ∑ τ ∈ cells X k, (∑ σ ∈ U X τ, m σ * φ σ) ^ 2 / m τ :=
    sum_nonneg (fun τ hτ => div_nonneg (sq_nonneg _) (hm.1 τ (mem_filter.mp hτ).1).le)
  have hN : ip X m (k + 1) φ φ = ∑ σ ∈ cells X (k + 1), m σ * φ σ * φ σ := rfl
  rw [hE]
  rw [hN] at hB ⊢
  have := mul_nonneg hlam0 hB0
  nlinarith [hT, hB, this]

theorem main_ind {X : Finset (Finset V)} {n : ℕ} (hX : IsPureComplex X n) {m : Finset V → ℝ}
    (hm : IsWeight X n m) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hexp : OneSidedLSE X m n lam) :
    ∀ k : ℕ, k + 1 ≤ n → ∀ φ : Finset V → ℝ, ip X m (k + 1) φ (fun _ => 1) = 0 →
      ip X m (k + 1 + 1) (dS X φ) (dS X φ) ≤
        ((k : ℝ) + 1 + ((k : ℝ) + 1) * ((k : ℝ) + 2) / 2 * lam) * ip X m (k + 1) φ φ := by
  have hdc := hX.1
  intro k
  induction k with
  | zero =>
    intro hk φ hφ
    have hA0 : ∑ τ ∈ cells X 0, ∑ σ ∈ U X τ, m σ * φ σ = 0 := by
      rw [sumU hdc 0 (fun σ => m σ * φ σ)]
      have : ∑ σ ∈ cells X (0 + 1), m σ * φ σ = 0 := by
        rw [← hφ]
        unfold ip
        apply sum_congr rfl
        intro σ _
        simp only [mul_one]
      rw [this, mul_zero]
    have hsub : cells X 0 ⊆ {∅} := by
      intro τ hτ
      simp only [cells, mem_filter, card_eq_zero] at hτ
      exact mem_singleton.mpr hτ.2
    have hB : ∑ τ ∈ cells X 0, (∑ σ ∈ U X τ, m σ * φ σ) ^ 2 / m τ = 0 := by
      rcases subset_singleton_iff.mp hsub with h | h
      · rw [h, sum_empty]
      · rw [h, sum_singleton] at hA0 ⊢
        rw [hA0]
        simp
    refine le_trans (step hX hm hlam0 hlam1 hexp hk φ 0 (by rw [hB, zero_mul])) (le_of_eq ?_)
    push_cast
    ring
  | succ j ih =>
    intro hk φ hφ
    have hj : j + 1 ≤ n := by omega
    have hpos := hm.1
    obtain ⟨ψ, hψ⟩ : ∃ ψ : Finset V → ℝ, ψ = fun τ => (∑ σ ∈ U X τ, m σ * φ σ) / m τ :=
      ⟨_, rfl⟩
    have hψ1 : ip X m (j + 1) ψ (fun _ => 1) = 0 := by
      unfold ip
      have : ∀ τ ∈ cells X (j + 1), m τ * ψ τ * (fun _ => (1:ℝ)) τ =
          ∑ σ ∈ U X τ, m σ * φ σ := by
        intro τ hτ
        have hmτ := (hpos τ (mem_filter.mp hτ).1).ne'
        rw [hψ]
        field_simp
      rw [sum_congr rfl this, sumU hdc (j + 1) (fun σ => m σ * φ σ)]
      have h0 : ∑ σ ∈ cells X (j + 1 + 1), m σ * φ σ = 0 := by
        rw [← hφ]
        unfold ip
        apply sum_congr rfl
        intro σ _
        simp only [mul_one]
      rw [h0, mul_zero]
    have hNψ : ip X m (j + 1) ψ ψ =
        ∑ τ ∈ cells X (j + 1), (∑ σ ∈ U X τ, m σ * φ σ) ^ 2 / m τ := by
      unfold ip
      apply sum_congr rfl
      intro τ hτ
      have hmτ := (hpos τ (mem_filter.mp hτ).1).ne'
      rw [hψ]
      field_simp
    have hadj : ip X m (j + 1) ψ ψ = ip X m (j + 1 + 1) φ (dS X ψ) := by
      unfold ip
      rw [ADJ X m (j + 1) φ ψ]
      apply sum_congr rfl
      intro τ hτ
      have hmτ := (hpos τ (mem_filter.mp hτ).1).ne'
      rw [hψ]
      field_simp
    have hCS := ip_cs hpos (j + 1 + 1) φ (dS X ψ)
    rw [← hadj] at hCS
    have hih := ih hj ψ hψ1
    have hNψ0 := ip_nonneg hpos (j + 1) ψ
    have hNφ0 := ip_nonneg hpos (j + 1 + 1) φ
    have hCj0 : 0 ≤ (j : ℝ) + 1 + ((j : ℝ) + 1) * ((j : ℝ) + 2) / 2 * lam :=
      add_nonneg (by positivity) (mul_nonneg (by positivity) hlam0)
    have hbound : ip X m (j + 1) ψ ψ ≤
        ((j : ℝ) + 1 + ((j : ℝ) + 1) * ((j : ℝ) + 2) / 2 * lam) * ip X m (j + 1 + 1) φ φ := by
      rcases eq_or_lt_of_le hNψ0 with h0 | hp
      · rw [← h0]
        exact mul_nonneg hCj0 hNφ0
      · have h1 := mul_le_mul_of_nonneg_left hih hNφ0
        have : ip X m (j + 1) ψ ψ * ip X m (j + 1) ψ ψ ≤
            ((j : ℝ) + 1 + ((j : ℝ) + 1) * ((j : ℝ) + 2) / 2 * lam) * ip X m (j + 1 + 1) φ φ *
              ip X m (j + 1) ψ ψ := by
          nlinarith [hCS, h1]
        exact le_of_mul_le_mul_right this hp
    refine le_trans (step hX hm hlam0 hlam1 hexp hk φ _ (by rw [← hNψ]; exact hbound))
      (le_of_eq ?_)
    push_cast
    ring

end HOW54


set_option backward.isDefEq.respectTransparency false

open HighOrderWalks.OneSided Finset

namespace WalksLocalInner

variable {V : Type*} [DecidableEq V]

lemma link_sum {X : Finset (Finset V)}
    (hdc : ∀ σ ∈ X, ∀ τ, τ ⊆ σ → τ ∈ X) (τ : Finset V) (r : ℕ) (F : Finset V → ℝ) :
    ∑ η ∈ cells (link X τ) r, F (τ ∪ η) =
      ∑ σ ∈ X.filter (fun σ => σ.card = τ.card + r ∧ τ ⊆ σ), F σ := by
  apply Finset.sum_nbij' (fun η => τ ∪ η) (fun σ => σ \ τ)
  · intro η hη
    simp only [cells, link, mem_filter] at hη ⊢
    obtain ⟨⟨_, hd, hu⟩, hr⟩ := hη
    exact ⟨hu, by rw [card_union_eq_card_add_card.mpr hd, hr], subset_union_left⟩
  · intro σ hσ
    simp only [cells, link, mem_filter] at hσ ⊢
    obtain ⟨hσX, hc, hsub⟩ := hσ
    refine ⟨⟨hdc σ hσX _ sdiff_subset, disjoint_sdiff, ?_⟩, ?_⟩
    · rw [union_sdiff_of_subset hsub]; exact hσX
    · have h := card_sdiff_add_card_eq_card hsub; omega
  · intro η hη
    simp only [cells, link, mem_filter] at hη
    exact union_sdiff_cancel_left hη.1.2.1
  · intro σ hσ
    exact union_sdiff_of_subset (mem_filter.mp hσ).2.2
  · intros; rfl

lemma localization_count {X : Finset (Finset V)}
    (hdc : ∀ σ ∈ X, ∀ τ, τ ⊆ σ → τ ∈ X) (c b : ℕ) (hcb : c ≤ b)
    (F : Finset V → ℝ) :
    (∑ τ ∈ cells X c, ∑ η ∈ cells (link X τ) (b - c), F (τ ∪ η)) =
      (Nat.choose b c : ℝ) * ∑ σ ∈ cells X b, F σ := by
  have hinner (τ : Finset V) (hτ : τ ∈ cells X c) :
      (∑ η ∈ cells (link X τ) (b - c), F (τ ∪ η)) =
        ∑ σ ∈ (cells X b).filter (fun σ => τ ⊆ σ), F σ := by
    rw [link_sum hdc]
    apply Finset.sum_congr
    · ext σ
      have hτc := (Finset.mem_filter.mp hτ).2
      simp [cells, hτc, Nat.add_sub_of_le hcb, and_assoc]
    · intros; rfl
  rw [Finset.sum_congr rfl hinner]
  rw [Finset.sum_comm' (t' := cells X b) (s' := fun σ => σ.powersetCard c)]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ hσ
    rw [Finset.sum_const, Finset.card_powersetCard, (Finset.mem_filter.mp hσ).2,
      nsmul_eq_mul]
  · intro τ σ
    simp only [cells, Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hτX, hτc⟩, ⟨hσX, hσb⟩, hsub⟩
      exact ⟨⟨hsub, hτc⟩, hσX, hσb⟩
    · rintro ⟨⟨hsub, hτc⟩, hσX, hσb⟩
      exact ⟨⟨hdc σ hσX τ hsub, hτc⟩, ⟨hσX, hσb⟩, hsub⟩

lemma local_inner {X : Finset (Finset V)}
    (hdc : ∀ σ ∈ X, ∀ τ, τ ⊆ σ → τ ∈ X) (m : Finset V → ℝ)
    (c b : ℕ) (hcb : c ≤ b) (φ ψ : Finset V → ℝ) :
    (Nat.choose b c : ℝ) * ip X m b φ ψ =
      ∑ τ ∈ cells X c, ip (link X τ) (linkWeight m τ) (b - c) (loc φ τ) (loc ψ τ) := by
  exact (localization_count hdc c b hcb (fun σ => m σ * φ σ * ψ σ)).symm

end WalksLocalInner

theorem HighOrderWalks.OneSided.proposition_4_1_1 {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (hX : IsPureComplex X n) (m : Finset V → ℝ) (hm : IsWeight X n m)
    (c l : ℕ) (hcl : c ≤ l) (hl : l ≤ n) (φ ψ : Finset V → ℝ) :
    (Nat.choose (l + 1) c : ℝ) * ip X m (l + 1) φ ψ =
      ∑ τ ∈ cells X c, ip (link X τ) (linkWeight m τ) (l + 1 - c) (loc φ τ) (loc ψ τ) := by
  exact WalksLocalInner.local_inner hX.1 m c (l + 1) (by omega) φ ψ



set_option backward.isDefEq.respectTransparency false

open HighOrderWalks.OneSided HOW54 Finset WalksLocalInner

namespace WalksLocalAdjoint

variable {V : Type*} [DecidableEq V]

lemma link_up_sum {X : Finset (Finset V)}
    (hdc : ∀ σ ∈ X, ∀ τ, τ ⊆ σ → τ ∈ X) (τ η : Finset V)
    (hη : η ∈ link X τ) (F : Finset V → ℝ) :
    (∑ σ ∈ U (link X τ) η, F (τ ∪ σ)) = ∑ ρ ∈ U X (τ ∪ η), F ρ := by
  obtain ⟨hηX, hdη, huη⟩ := Finset.mem_filter.mp hη
  have hcη := Finset.card_union_eq_card_add_card.mpr hdη
  apply Finset.sum_nbij' (fun σ => τ ∪ σ) (fun ρ => ρ \ τ)
  · intro σ hσ
    simp only [U, link, Finset.mem_filter] at hσ ⊢
    obtain ⟨⟨hσX, hdσ, huσ⟩, hσc, hησ⟩ := hσ
    refine ⟨huσ, ?_, Finset.union_subset_union (Finset.Subset.refl _) hησ⟩
    rw [Finset.card_union_eq_card_add_card.mpr hdσ, hcη, hσc]
    omega
  · intro ρ hρ
    simp only [U, link, Finset.mem_filter] at hρ ⊢
    obtain ⟨hρX, hρc, hsub⟩ := hρ
    have hτρ : τ ⊆ ρ := Finset.subset_union_left.trans hsub
    refine ⟨⟨hdc ρ hρX _ Finset.sdiff_subset, Finset.disjoint_sdiff, ?_⟩, ?_, ?_⟩
    · rw [Finset.union_sdiff_of_subset hτρ]; exact hρX
    · have h := Finset.card_sdiff_add_card_eq_card hτρ
      omega
    · intro v hv
      exact Finset.mem_sdiff.mpr ⟨hsub (Finset.mem_union_right _ hv),
        fun ht => Finset.disjoint_left.mp hdη ht hv⟩
  · intro σ hσ
    simp only [U, link, Finset.mem_filter] at hσ
    exact Finset.union_sdiff_cancel_left hσ.1.2.1
  · intro ρ hρ
    exact Finset.union_sdiff_of_subset (Finset.subset_union_left.trans (Finset.mem_filter.mp hρ).2.2)
  · intros; rfl

lemma local_dStar {X : Finset (Finset V)}
    (hdc : ∀ σ ∈ X, ∀ τ, τ ⊆ σ → τ ∈ X) (m : Finset V → ℝ)
    (τ η : Finset V) (hη : η ∈ link X τ) (φ : Finset V → ℝ) :
    dStar (link X τ) (linkWeight m τ) (loc φ τ) η = dStar X m φ (τ ∪ η) := by
  have huη := (Finset.mem_filter.mp hη).2.2
  have h := link_up_sum hdc τ η hη (fun ρ => m ρ / m (τ ∪ η) * φ ρ)
  simpa only [U, and_comm, dStar, if_pos hη, if_pos huη, linkWeight, loc] using h

end WalksLocalAdjoint

theorem HighOrderWalks.OneSided.proposition_4_1_2 {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (hX : IsPureComplex X n) (m : Finset V → ℝ) (hm : IsWeight X n m)
    (c l : ℕ) (hcl : c ≤ l) (hl : l ≤ n) (φ ψ : Finset V → ℝ) :
    (Nat.choose l c : ℝ) * ip X m l (dStar X m φ) (dStar X m ψ) =
      ∑ τ ∈ cells X c, ip (link X τ) (linkWeight m τ) (l - c)
        (dStar (link X τ) (linkWeight m τ) (loc φ τ))
        (dStar (link X τ) (linkWeight m τ) (loc ψ τ)) := by
  rw [WalksLocalInner.local_inner hX.1 m c l hcl]
  apply Finset.sum_congr rfl
  intro τ _
  unfold ip
  apply Finset.sum_congr rfl
  intro η hη
  rw [WalksLocalAdjoint.local_dStar hX.1 m τ η (Finset.mem_filter.mp hη).1,
    WalksLocalAdjoint.local_dStar hX.1 m τ η (Finset.mem_filter.mp hη).1]
  rfl



set_option backward.isDefEq.respectTransparency false

open HighOrderWalks.OneSided HOW54 Finset

namespace WalksLaplacianIdentity

variable {V : Type*} [DecidableEq V]

lemma ip_single (X : Finset (Finset V)) (m : Finset V → ℝ) (c : ℕ)
    (f : Finset V → ℝ) (τ : Finset V) (hτ : τ ∈ cells X c) :
    ip X m c f (Pi.single τ 1) = m τ * f τ := by
  classical
  simp [ip, Pi.single_apply, hτ]

lemma upper_identity (X : Finset (Finset V)) (n : ℕ) (hX : IsPureComplex X n)
    (m : Finset V → ℝ) (hm : IsWeight X n m) (k : ℕ) (hk : k + 1 ≤ n)
    (φ : Finset V → ℝ) (τ : Finset V) (hτ : τ ∈ cells X (k + 1)) :
    dStar X m (dS X φ) τ = ((k : ℝ) + 2) * upperWalk X m φ τ := by
  classical
  have hτX := (Finset.mem_filter.mp hτ).1
  have hmτ : m τ ≠ 0 := (hm.1 τ hτX).ne'
  have h := (key1a hX hm hk φ (Pi.single τ 1)).trans
    (key1b hm φ (Pi.single τ 1)).symm
  rw [ip_single X m (k + 1) _ τ hτ] at h
  have hl : ip X m (k + 1 + 1) (dS X φ) (dS X (Pi.single τ 1)) =
      m τ * dStar X m (dS X φ) τ := by
    unfold ip
    rw [ADJ X m (k + 1)]
    simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', hτ, if_true]
    rw [dStar, if_pos hτX, Finset.mul_sum]
    apply Finset.sum_congr
    · ext σ
      simp [U, and_comm]
    · intro σ _
      field_simp
  rw [hl] at h
  apply (mul_left_cancel₀ hmτ)
  calc
    _ = ((k : ℝ) + 1 + 1) * (m τ * upperWalk X m φ τ) := h
    _ = _ := by ring

def L (X : Finset (Finset V)) (τ : Finset V) : Finset (Finset V) :=
  X.filter (fun τ' => τ'.card = τ.card ∧ τ' ≠ τ ∧ τ ∩ τ' ∈ X ∧
    (τ ∩ τ').card + 1 = τ.card)

lemma intersection_eq {η τ τ' : Finset V} (hητ : η ⊆ τ) (hητ' : η ⊆ τ')
    (hη : η.card + 1 = τ.card) (hc : τ'.card = τ.card) (hne : τ' ≠ τ) :
    τ ∩ τ' = η := by
  have hproper : τ ∩ τ' ⊂ τ := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, ?_⟩
    intro he
    apply hne
    have hsub : τ ⊆ τ' := by rw [← he]; exact Finset.inter_subset_right
    exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  exact (Finset.eq_of_subset_of_card_le (Finset.subset_inter hητ hητ')
    (by have h := Finset.card_lt_card hproper; omega)).symm

lemma lower_sum (X : Finset (Finset V)) (m : Finset V → ℝ)
    (φ : Finset V → ℝ) (τ : Finset V) (hτ : τ ∈ X) :
    dS X (dStar X m φ) τ =
      (∑ η ∈ D X τ, m τ / m η) * φ τ +
        ∑ τ' ∈ L X τ, m τ' / m (τ ∩ τ') * φ τ' := by
  classical
  have hl : dS X (dStar X m φ) τ =
      ∑ η ∈ D X τ, (m τ / m η * φ τ +
        ∑ τ' ∈ (U X η).erase τ, m τ' / m η * φ τ') := by
    rw [dS, if_pos hτ]
    change (∑ η ∈ D X τ, dStar X m φ η) = _
    apply Finset.sum_congr rfl
    intro η hη
    obtain ⟨hηX, hητ, hc⟩ := Finset.mem_filter.mp hη
    have hτU : τ ∈ U X η := Finset.mem_filter.mpr ⟨hτ, hc.symm, hητ⟩
    rw [Finset.add_sum_erase _ (fun τ' => m τ' / m η * φ τ') hτU, dStar, if_pos hηX]
    apply Finset.sum_congr
    · ext σ
      simp [U, and_comm]
    · intros; rfl
  rw [hl, Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm' (t' := L X τ) (s' := fun τ' => {τ ∩ τ'})]
  · simp
  · intro η τ'
    simp only [D, U, L, Finset.mem_filter, Finset.mem_erase, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hηX, hητ, hηc⟩, hne, hτ'X, hτ'c, hητ'⟩
      have hi := intersection_eq hητ hητ' hηc (by omega) hne
      refine ⟨hi.symm, hτ'X, by omega, hne, ?_, ?_⟩
      · rw [hi]; exact hηX
      · rw [hi]; exact hηc
    · rintro ⟨rfl, hτ'X, hc, hne, hiX, hic⟩
      exact ⟨⟨hiX, Finset.inter_subset_left, hic⟩, hne, hτ'X, by omega,
        Finset.inter_subset_right⟩

lemma lower_identity (X : Finset (Finset V)) (m : Finset V → ℝ) (k : ℕ)
    (φ : Finset V → ℝ) (τ : Finset V) (hτ : τ ∈ cells X (k + 1)) :
    dS X (dStar X m φ) τ = ((k : ℝ) + 1) * lowerWalk X m φ τ := by
  classical
  obtain ⟨hτX, hτc⟩ := Finset.mem_filter.mp hτ
  have hc : (τ.card : ℝ) = (k : ℝ) + 1 := by exact_mod_cast hτc
  have hn : (τ.card : ℝ) ≠ 0 := by rw [hc]; positivity
  rw [lower_sum X m φ τ hτX, ← hc, lowerWalk, if_pos hτX, mul_add, ← mul_assoc,
    Finset.mul_sum, Finset.mul_sum]
  change (∑ η ∈ D X τ, m τ / m η) * φ τ +
      ∑ τ' ∈ L X τ, m τ' / m (τ ∩ τ') * φ τ' =
    (∑ η ∈ D X τ, (τ.card : ℝ) * (m τ / ((τ.card : ℝ) * m η))) * φ τ +
      ∑ τ' ∈ L X τ, (τ.card : ℝ) * (m τ' / ((τ.card : ℝ) * m (τ ∩ τ')) * φ τ')
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro η _
    field_simp
  · apply Finset.sum_congr rfl
    intro τ' _
    field_simp

end WalksLaplacianIdentity

theorem HighOrderWalks.OneSided.corollary_3_7 {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (hX : IsPureComplex X n) (m : Finset V → ℝ) (hm : IsWeight X n m)
    (k : ℕ) (hk : k + 1 ≤ n) (φ : Finset V → ℝ) :
    (∀ τ ∈ cells X (k + 1), dStar X m (dS X φ) τ = ((k : ℝ) + 2) * upperWalk X m φ τ) ∧
      (∀ τ ∈ cells X (k + 1), dS X (dStar X m φ) τ = ((k : ℝ) + 1) * lowerWalk X m φ τ) := by
  exact ⟨WalksLaplacianIdentity.upper_identity X n hX m hm k hk φ,
    WalksLaplacianIdentity.lower_identity X m k φ⟩



set_option backward.isDefEq.respectTransparency false

open HighOrderWalks.OneSided HOW54 Finset WalksLocalInner WalksLocalAdjoint

namespace WalksLinkDecomposition

variable {V : Type*} [DecidableEq V]

lemma lower_link_constant {X : Finset (Finset V)}
    (hdc : ∀ σ ∈ X, ∀ τ, τ ⊆ σ → τ ∈ X) (m : Finset V → ℝ)
    {τ : Finset V} (hτ : τ ∈ X) (φ : Finset V → ℝ)
    {η : Finset V} (hη : η ∈ cells (link X τ) 1) :
    lowerWalk (link X τ) (linkWeight m τ) (loc φ τ) η = dStar X m φ τ := by
  have he : (∅ : Finset V) ∈ link X τ := by
    simp only [link, mem_filter, Finset.disjoint_empty_right, union_empty, true_and]
    exact ⟨hdc τ hτ ∅ (empty_subset τ), hτ⟩
  have hD : D (link X τ) η = {∅} := by
    ext σ
    simp only [D, mem_filter, mem_singleton]
    constructor
    · intro h
      exact card_eq_zero.mp (by have := (mem_filter.mp hη).2; omega)
    · rintro rfl
      exact ⟨he, empty_subset η, by simpa using (mem_filter.mp hη).2.symm⟩
  have h := WalksLaplacianIdentity.lower_identity (link X τ) (linkWeight m τ) 0 (loc φ τ) η hη
  simp only [Nat.cast_zero, zero_add, one_mul] at h
  rw [← h, dS, if_pos (mem_filter.mp hη).1]
  change (∑ σ ∈ D (link X τ) η, dStar (link X τ) (linkWeight m τ) (loc φ τ) σ) = _
  rw [hD, sum_singleton, local_dStar hdc m τ ∅ he φ, union_empty]

lemma nonLazy_congr {X : Finset (Finset V)} (m : Finset V → ℝ)
    {φ ψ : Finset V → ℝ} (hfg : ∀ η ∈ cells X 1, φ η = ψ η)
    {η : Finset V} (hη : η ∈ cells X 1) :
    nonLazyWalk X m φ η = nonLazyWalk X m ψ η := by
  have hηX := (mem_filter.mp hη).1
  have hηc := (mem_filter.mp hη).2
  simp only [nonLazyWalk, upperWalk, if_pos hηX, hfg η hη]
  congr 3
  apply sum_congr rfl
  intro η' hη'
  rw [hfg η' (mem_filter.mpr ⟨(mem_filter.mp hη').1, (mem_filter.mp hη').2.1.trans hηc⟩)]

lemma link_pairing {X : Finset (Finset V)} (hdc : ∀ σ ∈ X, ∀ τ, τ ⊆ σ → τ ∈ X)
    {m : Finset V → ℝ} (hpos : ∀ σ ∈ X, 0 < m σ) {τ : Finset V} (f g : Finset V → ℝ) :
    ip (link X τ) (linkWeight m τ) 1 (nonLazyWalk (link X τ) (linkWeight m τ) (loc f τ))
        (loc g τ) =
      ∑ σ ∈ U X τ, ∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), m (σ ∪ σ') * f σ' * g σ := by
  unfold ip
  rw [← B1 hdc (fun σ => ∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), m (σ ∪ σ') * f σ' * g σ)]
  apply sum_congr rfl
  intro η hη
  have hη' := hη
  simp only [cells, link, mem_filter] at hη'
  obtain ⟨⟨hηX, hdη, huη⟩, hη1⟩ := hη'
  have hηL : η ∈ link X τ := mem_filter.mpr ⟨hηX, hdη, huη⟩
  have hw : linkWeight m τ η ≠ 0 := (hpos _ huη).ne'
  have hc : ((η.card : ℕ) : ℝ) = 1 := by rw [hη1]; norm_num
  rw [← B2 hdc hη (fun σ' => m (τ ∪ η ∪ σ') * f σ' * g (τ ∪ η))]
  have e : ∀ η' ∈ W (link X τ) η, m (τ ∪ η ∪ (τ ∪ η')) = linkWeight m τ (η ∪ η') := by
    intro η' _
    simp only [linkWeight]
    congr 1
    ext x; simp only [mem_union]; tauto
  have e' : ∑ η' ∈ W (link X τ) η, m (τ ∪ η ∪ (τ ∪ η')) * f (τ ∪ η') * g (τ ∪ η) =
      ∑ η' ∈ W (link X τ) η, linkWeight m τ (η ∪ η') * loc f τ η' * loc g τ η :=
    sum_congr rfl (fun η' h => by simp only [e η' h, loc])
  rw [e']
  simp only [nonLazyWalk, upperWalk, if_pos hηL, hc, W, div_mul_eq_mul_div, ← Finset.sum_div,
    ← Finset.sum_mul]
  first
    | (field_simp; ring)
    | field_simp

lemma weighted_dStar {X : Finset (Finset V)} {m : Finset V → ℝ}
    {τ : Finset V} (hτ : τ ∈ X) (hm : m τ ≠ 0) (φ : Finset V → ℝ) :
    (∑ σ ∈ U X τ, m σ * φ σ) = m τ * dStar X m φ τ := by
  rw [dStar, if_pos hτ, mul_sum]
  apply sum_congr
  · ext σ
    simp only [U, mem_filter, and_comm, and_left_comm]
  · intro σ _
    field_simp

lemma link_summand_formula {X : Finset (Finset V)} {n : ℕ}
    (hX : IsPureComplex X n) {m : Finset V → ℝ} (hm : IsWeight X n m)
    {k : ℕ} (hk : k + 1 ≤ n) {τ : Finset V} (hτ : τ ∈ cells X k)
    (φ ψ : Finset V → ℝ) :
    linkSummand X m τ φ ψ =
      (∑ σ ∈ U X τ, ∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'),
        m (σ ∪ σ') * φ σ' * ψ σ) - m τ * dStar X m φ τ * dStar X m ψ τ := by
  have hτX := (mem_filter.mp hτ).1
  have hτc := (mem_filter.mp hτ).2
  have hn : ∀ σ ∈ U X τ, σ.card ≤ n := by
    intro σ hσ
    have := (mem_filter.mp hσ).2.1
    omega
  have he : linkSummand X m τ φ ψ =
      ip (link X τ) (linkWeight m τ) 1
        (nonLazyWalk (link X τ) (linkWeight m τ) (loc (fun σ => φ σ - dStar X m φ τ) τ))
        (loc ψ τ) := by
    unfold linkSummand ip
    apply sum_congr rfl
    intro η hη
    congr 2
    apply nonLazy_congr _ _ hη
    intro η' hη'
    simp only [loc, lower_link_constant hX.1 m hτX φ hη']
  rw [he, link_pairing hX.1 hm.1]
  calc
    _ = ∑ σ ∈ U X τ,
        ((∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), m (σ ∪ σ') * φ σ' * ψ σ) -
          dStar X m φ τ * (m σ * ψ σ)) := by
      apply sum_congr rfl
      intro σ hσ
      have hw := R1 hX.1 hm hσ (hn σ hσ)
      calc
        _ = (∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), m (σ ∪ σ') * φ σ' * ψ σ) -
            dStar X m φ τ * ((∑ σ' ∈ (W X σ).filter (fun σ' => τ ⊆ σ'), m (σ ∪ σ')) * ψ σ) := by
          simp only [mul_sum, sum_mul, ← sum_sub_distrib]
          apply sum_congr rfl
          intro σ' _
          ring
        _ = _ := by rw [hw]
    _ = _ := by
      rw [sum_sub_distrib, ← mul_sum, weighted_dStar hτX (hm.1 τ hτX).ne' ψ]
      ring

end WalksLinkDecomposition

theorem WalksLinkDecomposition.proposition_4_2 {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (hX : IsPureComplex X n) (m : Finset V → ℝ) (hm : IsWeight X n m)
    (k : ℕ) (hk : k + 1 ≤ n) (φ ψ : Finset V → ℝ) :
    ip X m (k + 2) (dS X φ) (dS X ψ) =
      ip X m k (dStar X m φ) (dStar X m ψ) + ip X m (k + 1) φ ψ + linkTerm X m k φ ψ := by
  have ht : linkTerm X m k φ ψ =
      (∑ σ ∈ cells X (k + 1), ∑ σ' ∈ W X σ, m (σ ∪ σ') * φ σ' * ψ σ) -
        ip X m k (dStar X m φ) (dStar X m ψ) := by
    unfold linkTerm
    rw [sum_congr rfl (fun τ hτ => WalksLinkDecomposition.link_summand_formula hX hm hk hτ φ ψ),
      sum_sub_distrib, G2 hX.1 k]
    rfl
  rw [key1a hX hm hk φ ψ, ht]
  unfold ip
  ring




set_option backward.isDefEq.respectTransparency false

open HighOrderWalks.OneSided HighOrderWalks.TwoSided HighOrderWalks.TwoSided.Fresh
open scoped BigOperators

namespace WalksTwoLinkBilinear

variable {V : Type*} [DecidableEq V]

noncomputable def lowerLinear (X : Finset (Finset V)) (m : Finset V → ℝ) :
    (Finset V → ℝ) →ₗ[ℝ] (Finset V → ℝ) where
  toFun := lowerWalk X m
  map_add' f g := by
    funext σ
    by_cases hσ : σ ∈ X <;> simp [lowerWalk, hσ, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' a f := by
    funext σ
    change lowerWalk X m (fun η => a * f η) σ = a * lowerWalk X m f σ
    by_cases hσ : σ ∈ X
    · simp only [lowerWalk, if_pos hσ, Pi.smul_apply, smul_eq_mul]
      rw [mul_add]
      congr 1
      · ring
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro η _
        ring
    · simp [lowerWalk, hσ]

noncomputable def centerWalkLinear (X : Finset (Finset V)) (m : Finset V → ℝ) :
    (Finset V → ℝ) →ₗ[ℝ] (Finset V → ℝ) :=
  (nonLazyLinear X m).comp (LinearMap.id - lowerLinear X m)

noncomputable def localLinear (τ : Finset V) :
    (Finset V → ℝ) →ₗ[ℝ] (Finset V → ℝ) where
  toFun := fun f => loc f τ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma summand_add (X : Finset (Finset V)) (m : Finset V → ℝ) (τ : Finset V)
    (f g h : Finset V → ℝ) :
    linkSummand X m τ (f + g) h = linkSummand X m τ f h + linkSummand X m τ g h := by
  have he (a b : Finset V → ℝ) : linkSummand X m τ a b =
      ip (link X τ) (linkWeight m τ) 1
        (((centerWalkLinear (link X τ) (linkWeight m τ)).comp (localLinear τ)) a) (loc b τ) := rfl
  simp only [he, map_add, ip, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

lemma summand_smul (X : Finset (Finset V)) (m : Finset V → ℝ) (τ : Finset V)
    (a : ℝ) (f g : Finset V → ℝ) :
    linkSummand X m τ (a • f) g = a * linkSummand X m τ f g := by
  have he (u v : Finset V → ℝ) : linkSummand X m τ u v =
      ip (link X τ) (linkWeight m τ) 1
        (((centerWalkLinear (link X τ) (linkWeight m τ)).comp (localLinear τ)) u) (loc v τ) := rfl
  simp only [he, map_smul, ip, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro η _
  ring

lemma summand_symm {X : Finset (Finset V)} {n k : ℕ} {m : Finset V → ℝ}
    (hX : IsPureComplex X n) (hm : IsWeight X n m) (hk : k + 1 ≤ n)
    {τ : Finset V} (hτ : τ ∈ cells X k) (f g : Finset V → ℝ) :
    linkSummand X m τ f g = linkSummand X m τ g f := by
  rw [WalksLinkDecomposition.link_summand_formula hX hm hk hτ,
    WalksLinkDecomposition.link_summand_formula hX hm hk hτ]
  have he : (∑ σ ∈ HOW54.U X τ, ∑ σ' ∈ (HOW54.W X σ).filter (fun σ' => τ ⊆ σ'),
      m (σ ∪ σ') * f σ' * g σ) =
      ∑ σ ∈ HOW54.U X τ, ∑ σ' ∈ (HOW54.W X σ).filter (fun σ' => τ ⊆ σ'),
        m (σ ∪ σ') * g σ' * f σ := by
    rw [HOW54.SYM]
    apply Finset.sum_congr rfl
    intro σ _
    apply Finset.sum_congr rfl
    intro σ' _
    rw [Finset.union_comm σ' σ]
    ring
  rw [he]
  ring

lemma summand_polar {X : Finset (Finset V)} {n k : ℕ} {m : Finset V → ℝ}
    (hX : IsPureComplex X n) (hm : IsWeight X n m) (hk : k + 1 ≤ n)
    {τ : Finset V} (hτ : τ ∈ cells X k) (f g : Finset V → ℝ) (t : ℝ) :
    linkSummand X m τ (t • f + g) (t • f + g) -
      linkSummand X m τ (t • f - g) (t • f - g) = 4 * t * linkSummand X m τ f g := by
  have hs := summand_symm hX hm hk hτ
  have hr (u v w : Finset V → ℝ) : linkSummand X m τ u (v + w) =
      linkSummand X m τ u v + linkSummand X m τ u w := by
    rw [hs u (v + w), summand_add, hs v u, hs w u]
  have hmR (a : ℝ) (u v : Finset V → ℝ) : linkSummand X m τ u (a • v) = a * linkSummand X m τ u v := by
    rw [hs u (a • v), summand_smul, hs v u]
  have hsub : t • f - g = t • f + (-1 : ℝ) • g := by ext σ; simp; ring
  rw [hsub]
  simp only [summand_add, summand_smul, hr, hmR, hs g f]
  ring

lemma local_norm_polar (X : Finset (Finset V)) (m : Finset V → ℝ) (τ : Finset V)
    (f g : Finset V → ℝ) (t : ℝ) :
    ip (link X τ) (linkWeight m τ) 1 (loc (t • f + g) τ) (loc (t • f + g) τ) +
      ip (link X τ) (linkWeight m τ) 1 (loc (t • f - g) τ) (loc (t • f - g) τ) =
        2 * (t * t * ip (link X τ) (linkWeight m τ) 1 (loc f τ) (loc f τ) +
          ip (link X τ) (linkWeight m τ) 1 (loc g τ) (loc g τ)) := by
  unfold ip loc
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro η _
  ring

lemma local_bound {X : Finset (Finset V)} {n k : ℕ} {m : Finset V → ℝ} {b : ℝ}
    (hX : IsPureComplex X n) (hm : IsWeight X n m) (hk : k + 1 ≤ n)
    (hb0 : 0 ≤ b) (hb : LinkTwoSided X m k b) {τ : Finset V} (hτ : τ ∈ cells X k)
    (f g : Finset V → ℝ) :
    |linkSummand X m τ f g| ≤ b * nrm (link X τ) (linkWeight m τ) 1 (loc f τ) *
      nrm (link X τ) (linkWeight m τ) 1 (loc g τ) := by
  let A := ip (link X τ) (linkWeight m τ) 1 (loc f τ) (loc f τ)
  let C := ip (link X τ) (linkWeight m τ) 1 (loc g τ) (loc g τ)
  let B := linkSummand X m τ f g
  have hp : ∀ t : ℝ, 0 ≤ (b * A) * (t * t) + (-2 * B) * t + b * C := by
    intro t
    have h1 := linkSummand_bound hX hm hb0 hk hb hτ (t • f + g)
    have h2 := linkSummand_bound hX hm hb0 hk hb hτ (t • f - g)
    have hu := (abs_le.mp h1).2
    have hl := (abs_le.mp h2).1
    have hpol := summand_polar hX hm hk hτ f g t
    have hnorm := local_norm_polar X m τ f g t
    change 0 ≤ (b * A) * (t * t) + (-2 * B) * t + b * C
    dsimp only [A, B, C]
    have hnormb := congrArg (fun z : ℝ => b * z) hnorm
    nlinarith only [hu, hl, hpol, hnormb]
  have hd := discrim_le_zero hp
  simp only [discrim] at hd
  have hpos : ∀ η ∈ link X τ, 0 < linkWeight m τ η :=
    fun η hη => hm.1 _ (mem_link.mp hη).2.2
  have hA : 0 ≤ A := HOW54.ip_nonneg hpos 1 (loc f τ)
  have hC : 0 ≤ C := HOW54.ip_nonneg hpos 1 (loc g τ)
  change |B| ≤ b * Real.sqrt A * Real.sqrt C
  have hsA := Real.sq_sqrt hA
  have hsC := Real.sq_sqrt hC
  have hpR : 0 ≤ b * Real.sqrt A * Real.sqrt C := by positivity
  have hsq : (b * Real.sqrt A * Real.sqrt C) ^ 2 = b ^ 2 * A * C := by
    rw [mul_pow, mul_pow, hsA, hsC]
  nlinarith only [hd, hsq, sq_abs B, hpR, abs_nonneg B]

lemma rayleigh_parameter_nonneg {V : Type*} [DecidableEq V]
    (X : Finset (Finset V)) (n : ℕ) (hX : IsPureComplex X n)
    (m : Finset V → ℝ) (hm : IsWeight X n m) (lam : ℝ)
    (hRay : ∀ g : Finset V → ℝ, ip X m 1 g (fun _ => 1) = 0 →
      |ip X m 1 (nonLazyWalk X m g) g| ≤ lam * ip X m 1 g g) (hn : 1 ≤ n) : 0 ≤ lam := by
  obtain ⟨σ, hσ⟩ := hX.2.2.2
  obtain ⟨ρ, hρ, _, hcard⟩ := hX.2.2.1 σ hσ
  have htwo : 1 < ρ.card := by omega
  obtain ⟨u, huρ, v, hvρ, huv⟩ := Finset.one_lt_card.mp htwo
  have hu : ({u} : Finset V) ∈ X := hX.1 ρ hρ _ (Finset.singleton_subset_iff.mpr huρ)
  have hv : ({v} : Finset V) ∈ X := hX.1 ρ hρ _ (Finset.singleton_subset_iff.mpr hvρ)
  have huv' : ({u} : Finset V) ≠ {v} := by simpa using huv
  have huc : ({u} : Finset V) ∈ cells X 1 := mem_cells.mpr ⟨hu, by simp⟩
  have hvc : ({v} : Finset V) ∈ cells X 1 := mem_cells.mpr ⟨hv, by simp⟩
  have hempty : (∅ : Finset V) ∈ cells X 0 :=
    mem_cells.mpr ⟨hX.1 ρ hρ _ (Finset.empty_subset _), by simp⟩
  have hlink : link X (∅ : Finset V) = X := by
    ext τ
    simp [link]
  have hweight : linkWeight m (∅ : Finset V) = m := by
    funext τ
    simp [linkWeight]
  let g : Finset V → ℝ := fun τ => if τ = {u} then m {v} else if τ = {v} then -m {u} else 0
  have hgu : g {u} = m {v} := by simp [g]
  have hgv : g {v} = -m {u} := by simp [g, huv'.symm]
  have hgz : ∀ τ, τ ≠ {u} → τ ≠ {v} → g τ = 0 := by
    intro τ hτu hτv
    simp [g, hτu, hτv]
  have hmean : ip X m 1 g (fun _ => 1) = 0 := by
    unfold ip
    rw [sum_supported_pair (cells X 1) {u} {v} huv' huc hvc
      (fun τ => m τ * g τ * 1) (by
        intro τ _ hτu hτv
        simp [hgz τ hτu hτv])]
    rw [hgu, hgv]
    ring
  have hnorm : ip X m 1 g g = m {u} * m {v} * m {v} +
      m {v} * (-m {u}) * (-m {u}) := by
    unfold ip
    rw [sum_supported_pair (cells X 1) {u} {v} huv' huc hvc
      (fun τ => m τ * g τ * g τ) (by
        intro τ _ hτu hτv
        simp [hgz τ hτu hτv])]
    rw [hgu, hgv]
  have hmu : 0 < m {u} := hm.1 _ hu
  have hmv : 0 < m {v} := hm.1 _ hv
  have hpos : 0 < ip X m 1 g g := by
    rw [hnorm]
    have hp : 0 < m {u} * m {v} * m {v} := by positivity
    have hq : 0 ≤ m {v} * (-m {u}) * (-m {u}) := by
      have hh := mul_nonneg (le_of_lt hmv) (sq_nonneg (m {u}))
      nlinarith
    linarith
  have h := hRay g hmean
  have hprod : 0 ≤ lam * ip X m 1 g g := le_trans (abs_nonneg _) h
  exact nonneg_of_mul_nonneg_left hprod hpos


lemma link_parameter_nonneg {X : Finset (Finset V)} {n k : ℕ} {m : Finset V → ℝ} {b : ℝ}
    (hX : IsPureComplex X n) (hm : IsWeight X n m) (hk : k + 1 ≤ n)
    (hb : LinkTwoSided X m k b) : 0 ≤ b := by
  obtain ⟨σ, hσ⟩ := hX.2.2.2
  obtain ⟨ρ, hρ, _, hcρ⟩ := hX.2.2.1 σ hσ
  obtain ⟨τ, hτρ, hcτ⟩ := Finset.exists_subset_card_eq (by omega : k ≤ ρ.card)
  have hτX := hX.1 ρ hρ τ hτρ
  have hτ : τ ∈ cells X k := mem_cells.mpr ⟨hτX, hcτ⟩
  have hτn : τ.card ≤ n := by omega
  exact rayleigh_parameter_nonneg (link X τ) (n - τ.card) (link_isPure hX τ hτX hτn)
    (linkWeight m τ) (link_isWeight hX hm hτn) b (hb τ hτ) (by omega)

end WalksTwoLinkBilinear


/-- Lemma 4.3 (second inequality), p. 12: for `0 ≤ k ≤ n - 1` and `k`-cochains `φ, ψ`, if `b`
bounds `max{μ_k, -ν_k}` (for every `τ ∈ X(k-1)`, `|⟨(M')⁺_{τ,0} g, g⟩| ≤ b ‖g‖²` on the
`m_τ`-orthogonal complement of the constants), then
`Σ_{τ ∈ X(k-1)} |⟨(M')⁺_{τ,0}(I - M⁻_{τ,0}) φ_τ, ψ_τ⟩| ≤ (k+1) b ‖φ‖ ‖ψ‖`. -/
theorem solution {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (hX : HighOrderWalks.OneSided.IsPureComplex X n) (m : Finset V → ℝ) (hm : HighOrderWalks.OneSided.IsWeight X n m)
    (k : ℕ) (hk : k + 1 ≤ n) (b : ℝ) (hb : LinkTwoSided X m k b)
    (φ ψ : Finset V → ℝ) :
    ∑ τ ∈ HighOrderWalks.OneSided.cells X k, |HighOrderWalks.OneSided.linkSummand X m τ φ ψ| ≤
      ((k : ℝ) + 1) * b * HighOrderWalks.OneSided.nrm X m (k + 1) φ * HighOrderWalks.OneSided.nrm X m (k + 1) ψ := by
  have hb0 := WalksTwoLinkBilinear.link_parameter_nonneg hX hm hk hb
  let F := fun τ => nrm (link X τ) (linkWeight m τ) 1 (loc φ τ)
  let G := fun τ => nrm (link X τ) (linkWeight m τ) 1 (loc ψ τ)
  have hs (f : Finset V → ℝ) (τ : Finset V) :
      nrm (link X τ) (linkWeight m τ) 1 (loc f τ) ^ 2 =
        ip (link X τ) (linkWeight m τ) 1 (loc f τ) (loc f τ) := by
    exact Real.sq_sqrt (HOW54.ip_nonneg (fun η hη => hm.1 _ (mem_link.mp hη).2.2) 1 (loc f τ))
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (cells X k) F G
  have hF : (∑ τ ∈ cells X k, F τ ^ 2) = ((k : ℝ) + 1) * ip X m (k + 1) φ φ := by
    simp only [F, hs]
    exact localization_ip_sum hX m k φ φ
  have hG : (∑ τ ∈ cells X k, G τ ^ 2) = ((k : ℝ) + 1) * ip X m (k + 1) ψ ψ := by
    simp only [G, hs]
    exact localization_ip_sum hX m k ψ ψ
  rw [hF, hG] at hcs
  have he : Real.sqrt (((k : ℝ) + 1) * ip X m (k + 1) φ φ) *
      Real.sqrt (((k : ℝ) + 1) * ip X m (k + 1) ψ ψ) =
      ((k : ℝ) + 1) * nrm X m (k + 1) φ * nrm X m (k + 1) ψ := by
    rw [Real.sqrt_mul (by positivity : 0 ≤ (k : ℝ) + 1),
      Real.sqrt_mul (by positivity : 0 ≤ (k : ℝ) + 1)]
    have hsq := Real.sq_sqrt (by positivity : 0 ≤ (k : ℝ) + 1)
    unfold nrm
    calc
      _ = (Real.sqrt ((k : ℝ) + 1)) ^ 2 * Real.sqrt (ip X m (k + 1) φ φ) *
          Real.sqrt (ip X m (k + 1) ψ ψ) := by ring
      _ = _ := by rw [hsq]
  rw [he] at hcs
  calc
    _ ≤ ∑ τ ∈ cells X k, b * F τ * G τ :=
      Finset.sum_le_sum (fun τ hτ => WalksTwoLinkBilinear.local_bound hX hm hk hb0 hb hτ φ ψ)
    _ = b * ∑ τ ∈ cells X k, F τ * G τ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro τ _
      ring
    _ ≤ b * (((k : ℝ) + 1) * nrm X m (k + 1) φ * nrm X m (k + 1) ψ) :=
      mul_le_mul_of_nonneg_left hcs hb0
    _ = _ := by ring




#print axioms solution
