-- Prove2me | solution 1 for GlobalTheory.RelIndexOfMap.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:07:43.843561+00:00
-- url     : https://prove2.me/submissions/33ecaec6-a13c-4199-97fa-aeefaa24ae6d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RelIndexEqOfMap
import Theorems.Thm_GlobalTheory_RelIndexOfMap_relIndex_eq_of_map
import Theorems.Thm_GlobalTheory_RelIndexOfMap_relIndex_pi
import Theorems.Thm_GlobalTheory_RelIndexOfMap_mem_map_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.RelIndexOfMap
namespace GlobalTheory.RelIndexOfMap
theorem _root_.solution : (let d1 : {G : Type} → [inst : Group G] → (M N : Subgroup G) → Subgroup G → G → Subgroup ↥(Subgroup.subgroupOf N M) := @(fun {G : Type} [Group G] (M N K : Subgroup G) (x : G) ↦ Subgroup.comap (MonoidHom.comp (Subgroup.subtype M) (Subgroup.subtype (Subgroup.subgroupOf N M))) (Subgroup.comap (MulEquiv.toMonoidHom ((MulAut.conj : G → MulAut G) x⁻¹)) K)); ∀ {G : Type} [inst : Group G] {M N K : Subgroup G} {ι : Type} [inst_1 : Fintype ι] {H : ι → Type} [inst_2 : (i : ι) → Group (H i)] (S : Subgroup G) [Subgroup.Normal S] (L : (i : ι) → G →* H i) (J Nn : (i : ι) → Subgroup (H i)), (∀ k ∈ K, ∀ (i : ι), (L i : G → H i) k ∈ J i) → (∀ y ∈ S, (∀ (i : ι), (L i : G → H i) y ∈ J i) → y ∈ K) → S ≤ M → (∀ n ∈ N, ∀ (i : ι), (L i : G → H i) n ∈ Nn i) → (∀ y ∈ S, (∀ (i : ι), (L i : G → H i) y ∈ Nn i) → y ∈ N) → (∀ (u : (i : ι) → H i), ∃ y ∈ S, ∀ (i : ι), (L i : G → H i) y = u i) → ∀ {δ r : G}, r ∈ S → ∀ (c h : (i : ι) → H i), (∀ (i : ι), (L i : G → H i) r = c i * h i) → (∀ (i : ι), c i ∈ J i) → (∀ (i : ι) (x : H i), ((L i : G → H i) δ * c i)⁻¹ * x * ((L i : G → H i) δ * c i) ∈ Nn i ↔ x ∈ Nn i) → Subgroup.relIndex (d1 M N K (δ * r)) (d1 M N K δ) = ∏ i : ι, Subgroup.relIndex (Subgroup.map (MulEquiv.toMonoidHom ((MulAut.conj : H i → MulAut (H i)) (h i))) (J i)) (Nn i ⊓ J i) ∧ Subgroup.relIndex (d1 M N K δ) (d1 M N K (δ * r)) = ∏ i : ι, Subgroup.relIndex (J i) (Nn i ⊓ Subgroup.map (MulEquiv.toMonoidHom ((MulAut.conj : H i → MulAut (H i)) (h i))) (J i))) := by
  intro d1 G _ M N K ι _ H _ S hS L J Nn hKJ hSK hSM hNN hSN hsurj δ r hr c h hrc hc hδ
  have hd : ∀ (x : G) (n : N.subgroupOf M), n ∈ d1 M N K x ↔ x⁻¹ * ((n : M) : G) * x ∈ K := by
    intro x n
    simp [d1, Subgroup.mem_comap]
  have key : ∀ a b : G, a * b⁻¹ ∈ S → b ∈ K → (∀ i, L i a ∈ J i) → a ∈ K := by
    intro a b hab hb ha
    have : a * b⁻¹ ∈ K := hSK _ hab fun i => by
      rw [map_mul, map_inv]
      exact mul_mem (ha i) (inv_mem (hKJ b hb i))
    simpa using mul_mem this hb
  let φ : (N.subgroupOf M) →* (∀ i, H i) :=
    { toFun := fun n i => (L i δ * c i)⁻¹ * L i ((n : M) : G) * (L i δ * c i)
      map_one' := by ext i; simp
      map_mul' := by intro a b; ext i; simp [mul_assoc] }
  have hφ : ∀ n i, φ n i = (L i δ * c i)⁻¹ * L i ((n : M) : G) * (L i δ * c i) := fun _ _ => rfl
  have hφN : ∀ n i, φ n i ∈ Nn i := fun n i => (hδ i _).2 (hNN _ n.2 i)
  have h1 : ∀ n i, φ n i ∈ J i ↔ L i (δ⁻¹ * ((n : M) : G) * δ) ∈ J i := by
    intro n i
    have e : φ n i = (c i)⁻¹ * L i (δ⁻¹ * ((n : M) : G) * δ) * c i := by
      simp [hφ, mul_assoc]
    rw [e, Subgroup.mul_mem_cancel_right _ (hc i), Subgroup.mul_mem_cancel_left _ (inv_mem (hc i))]
  have h2 : ∀ n i, φ n i ∈
      Subgroup.map (MulEquiv.toMonoidHom ((MulAut.conj : H i → MulAut (H i)) (h i))) (J i) ↔
      L i ((δ * r)⁻¹ * ((n : M) : G) * (δ * r)) ∈ J i := by
    intro n i
    rw [mem_map_conj]
    have e : (h i)⁻¹ * φ n i * h i = L i ((δ * r)⁻¹ * ((n : M) : G) * (δ * r)) := by
      simp [hφ, hrc, mul_assoc]
    rw [e]
  have hs : ∀ u : ∀ i, H i, (∀ i, u i ∈ Nn i) →
      ∃ n : N.subgroupOf M, ((n : M) : G) ∈ S ∧ φ n = u := by
    intro u hu
    obtain ⟨y, hy, hyu⟩ := hsurj fun i => (L i δ * c i) * u i * (L i δ * c i)⁻¹
    have hyN : y ∈ N := hSN y hy fun i => by
      rw [← hδ i, hyu i]
      simpa [mul_assoc] using hu i
    refine ⟨⟨⟨y, hSM hy⟩, hyN⟩, hy, ?_⟩
    ext i
    rw [hφ]
    simp [hyu, mul_assoc]
  constructor
  · rw [← relIndex_pi]
    refine relIndex_eq_of_map φ _ _ _ _ ?_ ?_
    · ext u
      constructor
      · rintro ⟨n, hn, rfl⟩ i _
        exact ⟨hφN n i, (h1 n i).2 (hKJ _ ((hd _ _).1 hn) i)⟩
      · intro hu
        obtain ⟨n, hn, rfl⟩ := hs u fun i => (hu i trivial).1
        refine ⟨n, (hd _ _).2 (hSK _ ?_ fun i => (h1 n i).1 (hu i trivial).2), rfl⟩
        exact hS.conj_mem' _ hn _
    · intro a ha
      rw [hd] at ha ⊢
      constructor
      · intro hb i _
        exact (h2 a i).2 (hKJ _ hb i)
      · intro hb
        refine key _ _ ?_ ha fun i => (h2 a i).1 (hb i trivial)
        have := mul_mem (inv_mem hr) (hS.conj_mem _ hr (δ⁻¹ * ((a : M) : G) * δ))
        convert this using 1
        group
  · rw [← relIndex_pi]
    refine relIndex_eq_of_map φ _ _ _ _ ?_ ?_
    · ext u
      constructor
      · rintro ⟨n, hn, rfl⟩ i _
        exact ⟨hφN n i, (h2 n i).2 (hKJ _ ((hd _ _).1 hn) i)⟩
      · intro hu
        obtain ⟨n, hn, rfl⟩ := hs u fun i => (hu i trivial).1
        refine ⟨n, (hd _ _).2 (hSK _ ?_ fun i => (h2 n i).1 (hu i trivial).2), rfl⟩
        exact hS.conj_mem' _ hn _
    · intro a ha
      rw [hd] at ha ⊢
      constructor
      · intro hb i _
        exact (h1 a i).2 (hKJ _ hb i)
      · intro hb
        refine key _ _ ?_ ha fun i => (h1 a i).1 (hb i trivial)
        have := mul_mem (hS.conj_mem _ (inv_mem hr) (δ⁻¹ * ((a : M) : G) * δ)) hr
        convert this using 1
        group
end GlobalTheory.RelIndexOfMap
