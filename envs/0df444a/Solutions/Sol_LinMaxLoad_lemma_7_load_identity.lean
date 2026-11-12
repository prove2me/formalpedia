-- Prove2me | solution 1 for LinMaxLoad.lemma_7_load_identity
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:49:40.602417+00:00
-- url     : https://prove2.me/submissions/76224a9d-96bc-43fc-924e-72296c89e44c

import Mathlib
import Definitions.Def_LinMaxLoad_maxLoad
import Definitions.Def_LinMaxLoad_cosetSum

section
set_option autoImplicit false
namespace LinMaxLoad.Dev.LoadId

theorem card_le_maxLoad {A B : Type*} [DecidableEq B] (h : A → B) (S : Finset A) (b : B) :
    (S.filter fun a => h a = b).card ≤ LinMaxLoad.maxLoad h S := by
  by_cases hb : b ∈ S.image h
  · exact Finset.le_sup (f := fun b => (S.filter fun a => h a = b).card) hb
  · have : (S.filter fun a => h a = b) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro a ha hab
      exact hb (Finset.mem_image.mpr ⟨a, ha, hab⟩)
    rw [this]; simp

theorem mem_cosetSum {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Finite E]
    (V : Submodule K E) (T : Finset E) (y : E) :
    y ∈ LinMaxLoad.cosetSum V T ↔ ∃ t ∈ T, y - t ∈ V := by
  unfold LinMaxLoad.cosetSum
  rw [Set.Finite.mem_toFinset, Set.mem_add]
  constructor
  · rintro ⟨v, hv, t, ht, rfl⟩
    exact ⟨t, ht, by simpa using hv⟩
  · rintro ⟨t, ht, hy⟩
    exact ⟨y - t, hy, t, ht, by simp⟩

open Classical in
theorem fibre_card {K E : Type*} [Field K] [Fintype K] [AddCommGroup E] [Module K E] [Fintype E]
    {ℓ : ℕ} (V : Submodule K E) (h : E →ₗ[K] (Fin ℓ → K)) (x0 : E) :
    (Finset.univ.filter fun y : E => h y = h x0 ∧ V.mkQ y = V.mkQ x0).card =
      Nat.card (LinearMap.ker (h.domRestrict V)) := by
  classical
  have : Fintype (LinearMap.ker (h.domRestrict V)) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
  symm
  apply Finset.card_bij (fun (k : LinearMap.ker (h.domRestrict V)) _ => x0 + ((k : V) : E))
  · intro k _
    have hk : h ((k : V) : E) = 0 := LinearMap.mem_ker.mp k.2
    have hk2 : V.mkQ ((k : V) : E) = 0 := (Submodule.Quotient.mk_eq_zero V).mpr k.1.2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨by rw [map_add, hk, add_zero], by rw [map_add, hk2, add_zero]⟩
  · intro a _ b _ hab
    have : ((a : V) : E) = ((b : V) : E) := add_left_cancel hab
    exact Subtype.ext (Subtype.ext this)
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨hy1, hy2⟩ := hy
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hy2
    have hmem : y - x0 ∈ V := hy2
    refine ⟨⟨⟨y - x0, hmem⟩, ?_⟩, Finset.mem_univ _, ?_⟩
    · simp [LinearMap.mem_ker, hy1]
    · simp


theorem load_eq {K E : Type*} [Field K] [Fintype K] [AddCommGroup E] [Module K E] [Finite E]
    {ℓ : ℕ} (V : Submodule K E) (T : Finset E) (h : E →ₗ[K] (Fin ℓ → K))
    [DecidableEq (Fin ℓ → K)] [DecidableEq (E ⧸ V)] [DecidableEq ((Fin ℓ → K) ⧸ V.map h)] (b : Fin ℓ → K) :
    ((LinMaxLoad.cosetSum V T).filter fun y => h y = b).card =
      Nat.card (LinearMap.ker (h.domRestrict V)) *
        ((T.image V.mkQ).filter fun c =>
          Submodule.mapQ V (V.map h) h (Submodule.le_comap_map h V) c =
            Submodule.Quotient.mk b).card := by
  classical
  have : Fintype E := Fintype.ofFinite E
  rw [Finset.card_eq_sum_card_fiberwise (f := V.mkQ)
    (t := (T.image V.mkQ).filter fun c =>
          Submodule.mapQ V (V.map h) h (Submodule.le_comap_map h V) c =
            Submodule.Quotient.mk b)]
  · rw [Finset.sum_const_nat (m := Nat.card (LinearMap.ker (h.domRestrict V)))]
    · ring
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_image] at hc
      obtain ⟨⟨t, ht, rfl⟩, hg⟩ := hc
      rw [Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.eq] at hg
      obtain ⟨v0, hv0, hv0'⟩ := Submodule.mem_map.mp hg
      rw [← fibre_card V h (t - v0)]
      congr 1
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_cosetSum]
      have hx0 : h (t - v0) = b := by
        have : h t - b = h v0 := hv0'.symm
        rw [map_sub, ‹h t - b = h v0›.symm]; abel
      have hq : V.mkQ (t - v0) = V.mkQ t := by
        rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
        simpa using hv0
      rw [hx0, hq]
      constructor
      · rintro ⟨⟨_, hyb⟩, hyq⟩
        exact ⟨hyb, hyq⟩
      · rintro ⟨hyb, hyq⟩
        refine ⟨⟨⟨t, ht, ?_⟩, hyb⟩, hyq⟩
        rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hyq
        exact hyq
  · intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter, mem_cosetSum] at hy
    obtain ⟨⟨t, ht, hyt⟩, hyb⟩ := hy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_image]
    have hq : V.mkQ y = V.mkQ t := by
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      exact hyt
    refine ⟨⟨t, ht, hq.symm⟩, ?_⟩
    rw [Submodule.mkQ_apply, Submodule.mapQ_apply, hyb]

end LinMaxLoad.Dev.LoadId
namespace LinMaxLoad
open LinMaxLoad.Dev.LoadId in
open Classical in
theorem chk_lemma_7_load_identity {K E : Type*} [Field K] [Fintype K] [AddCommGroup E]
    [Module K E] [Finite E] (ℓ : ℕ) (V : Submodule K E) (T : Finset E)
    (h : E →ₗ[K] (Fin ℓ → K)) :
    maxLoad (h : E → Fin ℓ → K) (cosetSum V T) =
      Fintype.card K ^ Module.finrank K (LinearMap.ker (h.domRestrict V)) *
        maxLoad (Submodule.mapQ V (V.map h) h (Submodule.le_comap_map h V) :
          E ⧸ V → (Fin ℓ → K) ⧸ V.map h) (T.image V.mkQ) := by
  have hN : Fintype.card K ^ Module.finrank K (LinearMap.ker (h.domRestrict V)) =
      Nat.card (LinearMap.ker (h.domRestrict V)) := by
    rw [Module.natCard_eq_pow_finrank (K := K), Nat.card_eq_fintype_card]
  rw [hN]
  have hpos : 0 < Nat.card (LinearMap.ker (h.domRestrict V)) := Nat.card_pos
  apply le_antisymm
  · refine Finset.sup_le (fun b _ => ?_)
    rw [load_eq V T h b]
    convert Nat.mul_le_mul_left (Nat.card (LinearMap.ker (h.domRestrict V)))
      (card_le_maxLoad (Submodule.mapQ V (V.map h) h (Submodule.le_comap_map h V) :
          E ⧸ V → (Fin ℓ → K) ⧸ V.map h) (T.image V.mkQ) (Submodule.Quotient.mk b))
  · rcases Finset.eq_empty_or_nonempty
        ((T.image V.mkQ).image (Submodule.mapQ V (V.map h) h (Submodule.le_comap_map h V))) with he | hne
    · have : maxLoad (Submodule.mapQ V (V.map h) h (Submodule.le_comap_map h V) :
          E ⧸ V → (Fin ℓ → K) ⧸ V.map h) (T.image V.mkQ) = 0 := by
        unfold maxLoad; rw [he]; rfl
      rw [this]; simp
    · obtain ⟨c, hc, hsup⟩ := Finset.exists_mem_eq_sup _ hne
        (fun b => ((T.image V.mkQ).filter fun a =>
          Submodule.mapQ V (V.map h) h (Submodule.le_comap_map h V) a = b).card)
      have hM : maxLoad (Submodule.mapQ V (V.map h) h (Submodule.le_comap_map h V) :
          E ⧸ V → (Fin ℓ → K) ⧸ V.map h) (T.image V.mkQ) =
          ((T.image V.mkQ).filter fun a =>
          Submodule.mapQ V (V.map h) h (Submodule.le_comap_map h V) a = c).card := hsup
      rw [hM]
      obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hc'
      have e : Submodule.mapQ V (V.map h) h (Submodule.le_comap_map h V) (V.mkQ t) =
          Submodule.Quotient.mk (h t) := by
        rw [Submodule.mkQ_apply, Submodule.mapQ_apply]
      rw [e, ← load_eq V T h (h t)]
      apply card_le_maxLoad (h : E → Fin ℓ → K) (cosetSum V T) (h t)
end LinMaxLoad
end

theorem solution : type_of% @LinMaxLoad.chk_lemma_7_load_identity := @LinMaxLoad.chk_lemma_7_load_identity
