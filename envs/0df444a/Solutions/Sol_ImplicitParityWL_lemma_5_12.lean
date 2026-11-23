-- Prove2me | solution 1 for ImplicitParityWL.lemma_5_12
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:46:59.110527+00:00
-- url     : https://prove2.me/submissions/b68361d4-645e-4251-ad26-136cb168081f

import Mathlib
import Definitions.Def_ImplicitParityWL_SeedDescription

open ImplicitParityWL

namespace Aux_lemma_5_12

lemma zmod2_add_cancel_right (a b : ZMod 2) : a + b + b = a := by
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

lemma word_add_cancel_right {k ℓ : ℕ} (u v : Word k ℓ) : u + v + v = u := by
  ext c
  exact zmod2_add_cancel_right (u c) (v c)

lemma seedMap_color {k ℓ : ℕ} {W E : Type} (I : ImplicitSystem k ℓ W E)
    (D : SeedData k ℓ W E) (x : Vtx k ℓ W E) :
    (I.seedMap D x).color = x.color := by
  cases x <;> rfl

lemma seedMap_invol {k ℓ : ℕ} {W E : Type} (I : ImplicitSystem k ℓ W E)
    (D : SeedData k ℓ W E) (x : Vtx k ℓ W E) :
    I.seedMap D (I.seedMap D x) = x := by
  cases x <;> simp [ImplicitSystem.seedMap, zmod2_add_cancel_right, word_add_cancel_right]

lemma trackBit_diff {k ℓ : ℕ} {W E : Type} (I : ImplicitSystem k ℓ W E)
    (D : SeedData k ℓ W E) (e : E) {h : ℕ} (hh : 1 ≤ h) (c : Coord k ℓ) :
    I.trackBit D e (h - 1) c + I.trackBit D e h c = D.x e h c := by
  unfold ImplicitSystem.trackBit
  set base := match (I.schema e).third with
    | none => D.z (I.schema e).u ((I.schema e).σ c)
    | some _ => D.z (I.schema e).u ((I.schema e).σ c) + D.z (I.schema e).v ((I.schema e).τ c)
  have hIcc : Finset.Icc 1 h = insert h (Finset.Icc 1 (h - 1)) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnotmem : h ∉ Finset.Icc 1 (h - 1) := by
    simp only [Finset.mem_Icc]
    omega
  rw [hIcc, Finset.sum_insert hnotmem]
  set s := ∑ i ∈ Finset.Icc 1 (h - 1), D.x e i c
  calc (base + s) + (base + (D.x e h c + s))
      = (base + base) + (s + s) + D.x e h c := by ring
    _ = D.x e h c := by simp [CharTwo.add_self_eq_zero]

lemma seedMap_track {k ℓ : ℕ} {W E : Type} (I : ImplicitSystem k ℓ W E)
    {A : Finset (CColor k ℓ W E)} {α : W × Address k ℓ → ZMod 2} {D : SeedData k ℓ W E}
    (hD : I.IsSeedDescription A α D) {e : E} {c : Coord k ℓ} (hc : c ∈ I.Ie A e)
    {h' : ℕ} (hh' : h' ≤ k + 2) (r : ZMod 2) :
    I.seedMap D (I.track e h' c r) = I.track e h' c (r + I.trackBit D e h' c) := by
  by_cases h0 : h' = 0
  · subst h0
    have hIcc0 : Finset.Icc 1 0 = ∅ := by simp
    rcases hth : (I.schema e).third with _ | ⟨w, π⟩ <;>
      simp [ImplicitSystem.track, ImplicitSystem.trackBit, ImplicitSystem.seedMap, hth, hIcc0]
  · by_cases hk2 : h' = k + 2
    · subst hk2
      have hne0 : k + 2 ≠ 0 := by omega
      unfold ImplicitSystem.track ImplicitSystem.trackBit
      simp only [hne0, ↓reduceIte]
      have hms := hD.mask_sum e c hc
      rw [hms]
      rcases hth : (I.schema e).third with _ | ⟨w, π⟩
      · simp only [ImplicitSystem.seedMap, add_zero]
        congr 1
        set zu := D.z (I.schema e).u ((I.schema e).σ c)
        set zv := D.z (I.schema e).v ((I.schema e).τ c)
        calc r + zv = r + ((zu + zu) + zv) := by simp [CharTwo.add_self_eq_zero]
          _ = r + (zu + (zu + zv)) := by ring
      · simp only [ImplicitSystem.seedMap]
        congr 1
        set zu := D.z (I.schema e).u ((I.schema e).σ c)
        set zv := D.z (I.schema e).v ((I.schema e).τ c)
        set zw := D.z w (π c)
        calc r + zw = r + ((zu + zu) + (zv + zv) + zw) := by simp [CharTwo.add_self_eq_zero]
          _ = r + (zu + zv + (zu + zv + zw)) := by ring
    · unfold ImplicitSystem.track
      simp only [h0, hk2, ↓reduceIte, ImplicitSystem.seedMap]

lemma seedMap_edge {k ℓ : ℕ} {W E : Type} (I : ImplicitSystem k ℓ W E)
    {A : Finset (CColor k ℓ W E)} {α : W × Address k ℓ → ZMod 2} {D : SeedData k ℓ W E}
    (hD : I.IsSeedDescription A α D) {x y : Vtx k ℓ W E} (hxA : x.color ∈ A)
    (hxV : ∃ ε, I.IsVertex ε x) (he : I.Edge x y) :
    I.Edge (I.seedMap D x) (I.seedMap D y) := by
  cases he with
  | junc_u e c s t =>
    exact ImplicitSystem.Edge.junc_u e c _ _
  | junc_v e c s t =>
    exact ImplicitSystem.Edge.junc_v e c _ _
  | junc_sum e c s t =>
    obtain ⟨ε, hsome, _⟩ := hxV
    rcases hth : (I.schema e).third with _ | ⟨w, π⟩
    · simp [hth] at hsome
    · simp only [ImplicitSystem.seedMap, ImplicitSystem.trackBit, hth]
      have hIcc0 : Finset.Icc 1 0 = ∅ := by simp
      rw [hIcc0]
      simp only [Finset.sum_empty, add_zero]
      have hring : (s + D.z (I.schema e).u ((I.schema e).σ c)) +
          (t + D.z (I.schema e).v ((I.schema e).τ c)) =
          s + t + (D.z (I.schema e).u ((I.schema e).σ c) + D.z (I.schema e).v ((I.schema e).τ c)) := by
        ring
      rw [← hring]
      exact ImplicitSystem.Edge.junc_sum e c _ _
  | upd_prev e h c s t =>
    obtain ⟨ε, h1, hk2, hcdom⟩ := hxV
    have hcIe : c ∈ I.Ie A e := ⟨hcdom, Or.inr (Or.inl ⟨h, h1, hk2, hxA⟩)⟩
    rw [seedMap_track I hD hcIe (by omega)]
    exact ImplicitSystem.Edge.upd_prev e h c _ _
  | upd_next e h c s t =>
    obtain ⟨ε, h1, hk2, hcdom⟩ := hxV
    have hcIe : c ∈ I.Ie A e := ⟨hcdom, Or.inr (Or.inl ⟨h, h1, hk2, hxA⟩)⟩
    rw [seedMap_track I hD hcIe hk2]
    exact ImplicitSystem.Edge.upd_next e h c _ _
  | upd_msk e h c s t m hm =>
    obtain ⟨ε, h1, _, _⟩ := hxV
    simp only [ImplicitSystem.seedMap]
    apply ImplicitSystem.Edge.upd_msk
    have hdiff := trackBit_diff I D e h1 c
    calc (s + I.trackBit D e (h - 1) c) + (t + I.trackBit D e h c)
        = (s + t) + (I.trackBit D e (h - 1) c + I.trackBit D e h c) := by ring
      _ = m c + D.x e h c := by rw [hm, hdiff]
      _ = (m + D.x e h) c := rfl

lemma seedMap_isVertex_iff {k ℓ : ℕ} {W E : Type} (I : ImplicitSystem k ℓ W E)
    {A : Finset (CColor k ℓ W E)} {α : W × Address k ℓ → ZMod 2} {D : SeedData k ℓ W E}
    (hD : I.IsSeedDescription A α D) {x : Vtx k ℓ W E} (hxA : x.color ∈ A) :
    I.IsVertex 0 x ↔ I.IsVertex 1 (I.seedMap D x) := by
  cases x with
  | crd v c s =>
    simp only [ImplicitSystem.seedMap, ImplicitSystem.IsVertex, zero_mul, one_mul, ite_self]
    constructor
    · rintro ⟨hc, hinit⟩
      refine ⟨hc, fun b hb => ?_⟩
      have hs0 := hinit b hb
      have hz := hD.init v b hb c (Or.inl ⟨hc, hxA⟩)
      rw [hs0, zero_add, hz]
    · rintro ⟨hc, hinit⟩
      refine ⟨hc, fun b hb => ?_⟩
      have hs1 := hinit b hb
      have hz := hD.init v b hb c (Or.inl ⟨hc, hxA⟩)
      rw [← hz] at hs1
      have : s + D.z v c = 0 + D.z v c := by rw [zero_add]; exact hs1
      exact add_right_cancel this
  | sum e c t => rfl
  | junc e c s t => rfl
  | trk e h c s => rfl
  | upd e h c s t => rfl
  | msk e h m =>
    simp only [ImplicitSystem.seedMap, ImplicitSystem.IsVertex]
    constructor
    · rintro ⟨h1, hk2, hm⟩
      exact ⟨h1, hk2, (maskSpace (I.schema e).dom).add_mem hm (hD.mask e h h1 hk2)⟩
    · rintro ⟨h1, hk2, hm⟩
      refine ⟨h1, hk2, ?_⟩
      have hmem := (maskSpace (I.schema e).dom).add_mem hm (hD.mask e h h1 hk2)
      rwa [word_add_cancel_right] at hmem

end Aux_lemma_5_12

theorem solution (k ℓ : ℕ) (_hk : 3 ≤ k) (_hℓ : 1 ≤ ℓ) {W E : Type} [Fintype W] [Fintype E]
    (I : ImplicitSystem k ℓ W E) (A : Finset (CColor k ℓ W E)) (_hA : A.card ≤ k + 1)
    (α : W × Address k ℓ → ZMod 2) (D : SeedData k ℓ W E) (hD : I.IsSeedDescription A α D) :
    ∃ f : {p : I.Vertex 0 // p.val.color ∈ A} ≃ {q : I.Vertex 1 // q.val.color ∈ A},
      (∀ p, (f p).val.val = I.seedMap D p.val.val) ∧
      (∀ p, (f p).val.val.color = p.val.val.color) ∧
      (∀ p p', (I.graph 0).graph.Adj p.val p'.val ↔ (I.graph 1).graph.Adj (f p).val (f p').val) := by
  let f : {p : I.Vertex 0 // p.val.color ∈ A} ≃ {q : I.Vertex 1 // q.val.color ∈ A} :=
    { toFun := fun p =>
        ⟨⟨I.seedMap D p.1.1, (Aux_lemma_5_12.seedMap_isVertex_iff I hD p.2).mp p.1.2⟩,
          by rw [Aux_lemma_5_12.seedMap_color]; exact p.2⟩
      invFun := fun q =>
        ⟨⟨I.seedMap D q.1.1, by
            have h := q.1.2
            rw [← Aux_lemma_5_12.seedMap_invol I D q.1.1] at h
            exact (Aux_lemma_5_12.seedMap_isVertex_iff I hD
              (by rw [Aux_lemma_5_12.seedMap_color]; exact q.2)).mpr h⟩,
          by rw [Aux_lemma_5_12.seedMap_color]; exact q.2⟩
      left_inv := fun p => by
        ext1; ext1
        exact Aux_lemma_5_12.seedMap_invol I D p.1.1
      right_inv := fun q => by
        ext1; ext1
        exact Aux_lemma_5_12.seedMap_invol I D q.1.1 }
  have hf_val : ∀ p, (f p).1.1 = I.seedMap D p.1.1 := fun _ => rfl
  refine ⟨f, hf_val, fun p => Aux_lemma_5_12.seedMap_color I D p.1.1, ?_⟩
  intro p p'
  simp only [ImplicitSystem.graph, SimpleGraph.comap_adj, SimpleGraph.fromRel_adj]
  have hne_iff : p.1.1 ≠ p'.1.1 ↔ (f p).1.1 ≠ (f p').1.1 := by
    constructor
    · intro hne heq
      apply hne
      have := congrArg (I.seedMap D) heq
      rwa [hf_val, hf_val, Aux_lemma_5_12.seedMap_invol, Aux_lemma_5_12.seedMap_invol] at this
    · intro hne heq
      exact hne (by rw [hf_val, hf_val, heq])
  constructor
  · rintro ⟨hne, he | he⟩
    · exact ⟨hne_iff.mp hne, Or.inl (Aux_lemma_5_12.seedMap_edge I hD p.2 ⟨0, p.1.2⟩ he)⟩
    · exact ⟨hne_iff.mp hne, Or.inr (Aux_lemma_5_12.seedMap_edge I hD p'.2 ⟨0, p'.1.2⟩ he)⟩
  · rintro ⟨hne, he | he⟩
    · refine ⟨hne_iff.mpr hne, Or.inl ?_⟩
      have h' := Aux_lemma_5_12.seedMap_edge I hD (f p).2 ⟨1, (f p).1.2⟩ he
      rwa [hf_val, hf_val, Aux_lemma_5_12.seedMap_invol, Aux_lemma_5_12.seedMap_invol] at h'
    · refine ⟨hne_iff.mpr hne, Or.inr ?_⟩
      have h' := Aux_lemma_5_12.seedMap_edge I hD (f p').2 ⟨1, (f p').1.2⟩ he
      rwa [hf_val, hf_val, Aux_lemma_5_12.seedMap_invol, Aux_lemma_5_12.seedMap_invol] at h'
