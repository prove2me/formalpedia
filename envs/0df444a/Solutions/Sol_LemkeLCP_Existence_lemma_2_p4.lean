-- Prove2me | solution 1 for LemkeLCP.Existence.lemma_2_p4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T17:19:59.027215+00:00
-- url     : https://prove2.me/submissions/b423dda4-5ba7-4cb8-b4f1-18868be9a297

import Mathlib
import Definitions.Def_LemkeLCP_Existence_Setting
open Matrix


namespace LemkeLCP.Existence

section cone
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def coneOn (g : κ → E) (s : Finset κ) : Set E :=
  {y | ∃ x : κ → ℝ, 0 ≤ x ∧ y = ∑ i ∈ s, x i • g i}

theorem coneOn_closed_of_indep (g : κ → E) (s : Finset κ)
    (hind : ∀ c : κ → ℝ, ∑ i ∈ s, c i • g i = 0 → ∀ i ∈ s, c i = 0) :
    IsClosed (coneOn g s) := by
  let V : Submodule ℝ (κ → ℝ) :=
    { carrier := {x | ∀ i, i ∉ s → x i = 0}
      add_mem' := fun {a b} ha hb i hi => by simp [ha i hi, hb i hi]
      zero_mem' := fun i _ => rfl
      smul_mem' := fun c x hx i hi => by simp [hx i hi] }
  let T0 : (κ → ℝ) →ₗ[ℝ] E := ∑ i ∈ s, (LinearMap.proj i : (κ → ℝ) →ₗ[ℝ] ℝ).smulRight (g i)
  have hT0 : ∀ x, T0 x = ∑ i ∈ s, x i • g i := by
    intro x; simp [T0, LinearMap.sum_apply]
  let T : V →ₗ[ℝ] E := T0.domRestrict V
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h0 : ∑ i ∈ s, x.1 i • g i = 0 := by rw [← hT0]; exact hx
    have := hind x.1 h0
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ s
    · exact this i hi
    · exact x.2 i hi
  have hemb := LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.2 hinj)
  have hVclosed : IsClosed {x : V | 0 ≤ x.1} :=
    isClosed_le continuous_const ((continuous_subtype_val))
  have himg := hemb.isClosedMap _ hVclosed
  convert himg using 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨fun i => if i ∈ s then x i else 0, fun i hi => by simp [hi]⟩, ?_, ?_⟩
    · intro i; show (0:ℝ) ≤ (if i ∈ s then x i else 0)
      split_ifs
      · exact hx i
      · exact le_rfl
    · show T0 _ = _
      rw [hT0]; apply Finset.sum_congr rfl; intro i hi; simp [hi]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.1, hx, ?_⟩
    exact (hT0 x.1).symm.trans (by rfl) |>.symm

theorem coneOn_closed (g : κ → E) (s : Finset κ) : IsClosed (coneOn g s) := by
  induction' hn : s.card using Nat.strong_induction_on with n ih generalizing s
  by_cases hind : ∀ c : κ → ℝ, ∑ i ∈ s, c i • g i = 0 → ∀ i ∈ s, c i = 0
  · exact coneOn_closed_of_indep g s hind
  · push Not at hind
    obtain ⟨c0, hc0, j0, hj0, hne⟩ := hind
    -- get c with a positive entry
    obtain ⟨c, hc, hpos⟩ : ∃ c : κ → ℝ, ∑ i ∈ s, c i • g i = 0 ∧ ∃ i ∈ s, 0 < c i := by
      rcases lt_or_gt_of_ne hne with h | h
      · refine ⟨-c0, ?_, j0, hj0, by simpa using h⟩
        simp [neg_smul, Finset.sum_neg_distrib, hc0]
      · exact ⟨c0, hc0, j0, hj0, h⟩
    have hcover : coneOn g s = ⋃ j ∈ s, coneOn g (s.erase j) := by
      apply Set.Subset.antisymm
      · rintro y ⟨x, hx, rfl⟩
        obtain ⟨i0, hi0, hci0⟩ := hpos
        have hne' : (s.filter (fun i => 0 < c i)).Nonempty := ⟨i0, by simp [hi0, hci0]⟩
        obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image _ (fun i => x i / c i) hne'
        simp only [Finset.mem_filter] at hj hmin
        set t := x j / c j with ht
        have ht0 : 0 ≤ t := div_nonneg (hx j) hj.2.le
        simp only [Set.mem_iUnion]
        refine ⟨j, hj.1, fun i => if i ∈ s then x i - t * c i else x i, ?_, ?_⟩
        · intro i
          show (0:ℝ) ≤ (if i ∈ s then x i - t * c i else x i)
          by_cases his : i ∈ s
          · rw [if_pos his]
            by_cases hci : 0 < c i
            · have := hmin i ⟨his, hci⟩
              have h2 : t * c i ≤ x i := by
                have := (le_div_iff₀ hci).mp this; linarith
              linarith
            · have : c i ≤ 0 := not_lt.mp hci
              have hxi : 0 ≤ x i := hx i
              nlinarith [mul_nonneg ht0 (neg_nonneg.2 this)]
          · rw [if_neg his]; exact hx i
        · have hxj : (if j ∈ s then x j - t * c j else x j) = 0 := by
            rw [if_pos hj.1, ht]; field_simp [hj.2.ne']; ring
          have hf : (fun i => (if i ∈ s then x i - t * c i else x i) • g i) j = 0 := by
            show (if j ∈ s then x j - t * c j else x j) • g j = 0
            rw [hxj, zero_smul]
          rw [Finset.sum_erase s hf]
          have : ∑ i ∈ s, (if i ∈ s then x i - t * c i else x i) • g i
              = ∑ i ∈ s, x i • g i - t • ∑ i ∈ s, c i • g i := by
            rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl; intro i hi
            simp [hi, sub_smul, mul_smul]
          rw [this, hc]; simp
      · exact Set.iUnion₂_subset fun j hj => by
          rintro y ⟨x, hx, rfl⟩
          refine ⟨fun i => if i = j then 0 else x i, ?_, ?_⟩
          · intro i; show (0:ℝ) ≤ (if i = j then 0 else x i); split_ifs
            · exact le_rfl
            · exact hx i
          · have hf : (fun i => (if i = j then (0:ℝ) else x i) • g i) j = 0 := by simp
            rw [← Finset.sum_erase s hf]
            apply Finset.sum_congr rfl; intro i hi
            simp [(Finset.mem_erase.mp hi).1]
    rw [hcover]
    exact isClosed_biUnion_finset fun j hj => ih _ (by rw [← hn]; exact Finset.card_erase_lt_of_mem hj) _ rfl
end cone

theorem farkas_core {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (q : ι → ℝ) :
    Z M q = ∅ ↔ ∃ u : ι → ℝ, 0 ≤ u ∧ Mᵀ *ᵥ u ≤ 0 ∧ 0 < u ⬝ᵥ q := by
  constructor
  · intro hZ
    let g : ι ⊕ ι → (ι → ℝ) := Sum.elim (fun j i => M i j) (fun i => -(fun j => if i = j then (1:ℝ) else 0))
    have hK := coneOn_closed g Finset.univ
    have hconv : Convex ℝ (coneOn g Finset.univ) := by
      intro a ha b hb s t hs ht hst
      obtain ⟨x, hx, rfl⟩ := ha
      obtain ⟨x', hx', rfl⟩ := hb
      refine ⟨s • x + t • x', ?_, ?_⟩
      · intro k
        show (0:ℝ) ≤ s * x k + t * x' k
        have := hx k; have := hx' k
        have h1 : (0:ℝ) ≤ x k := hx k
        have h2 : (0:ℝ) ≤ x' k := hx' k
        positivity
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, Finset.sum_add_distrib, mul_smul,
          Finset.smul_sum]
    have hq : q ∉ coneOn g Finset.univ := by
      rintro ⟨x, hx, hq⟩
      have : (fun j => x (Sum.inl j)) ∈ Z M q := by
        have hqi : ∀ i, q i = (M *ᵥ (fun j => x (Sum.inl j))) i - x (Sum.inr i) := by
          intro i
          rw [hq]
          simp [g, Fintype.sum_sum_type, mulVec, dotProduct, mul_comm, Finset.sum_apply]
          ring
        refine ⟨fun j => hx _, fun i => ?_⟩
        have := hx (Sum.inr i)
        show (0:ℝ) ≤ (M *ᵥ (fun j => x (Sum.inl j)) - q) i
        rw [Pi.sub_apply, hqi i]
        have h2 : (0:ℝ) ≤ x (Sum.inr i) := this
        linarith
      rw [hZ] at this; exact this
    obtain ⟨f, u, hfu, hfq⟩ := geometric_hahn_banach_closed_point hconv hK hq
    have h0 : (0:ℝ) < u := by
      have := hfu 0 ⟨0, le_rfl, by simp⟩
      simpa using this
    have hneg : ∀ a ∈ coneOn g Finset.univ, f a ≤ 0 := by
      intro a ha
      by_contra hpos
      have hpos : 0 < f a := not_le.mp hpos
      obtain ⟨x, hx, rfl⟩ := ha
      have hmem : ((u + 1) / f (∑ i, x i • g i)) • (∑ i, x i • g i) ∈ coneOn g Finset.univ := by
        refine ⟨((u + 1) / f (∑ i, x i • g i)) • x, ?_, ?_⟩
        · intro k
          show (0:ℝ) ≤ (u + 1) / f (∑ i, x i • g i) * x k
          have : (0:ℝ) ≤ x k := hx k
          have : 0 ≤ (u + 1) / f (∑ i, x i • g i) := div_nonneg (by linarith) hpos.le
          positivity
        · simp [Finset.smul_sum, mul_smul]
      have := hfu _ hmem
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hpos.ne'] at this
      linarith
    have hfx : ∀ y : ι → ℝ, f y = y ⬝ᵥ (fun i => f (fun j => if i = j then (1:ℝ) else 0)) := by
      intro y
      have h := LinearMap.pi_apply_eq_sum_univ f.toLinearMap y
      simp only [ContinuousLinearMap.coe_coe] at h
      rw [h]
      simp [dotProduct]
    refine ⟨fun i => f (fun j => if i = j then (1:ℝ) else 0), ?_, ?_, ?_⟩
    · intro i
      have := hneg (g (Sum.inr i)) ⟨(Pi.single (Sum.inr i) (1:ℝ) : ι ⊕ ι → ℝ), ?_, ?_⟩
      · simp only [g, Sum.elim_inr, map_neg] at this
        show (0:ℝ) ≤ _
        linarith
      · intro k; show (0:ℝ) ≤ (Pi.single (Sum.inr i) (1:ℝ) : ι ⊕ ι → ℝ) k
        by_cases h : k = Sum.inr i <;> simp [Pi.single_apply, h]
      · simp [Pi.single_apply]
    · intro j
      have := hneg (g (Sum.inl j)) ⟨(Pi.single (Sum.inl j) (1:ℝ) : ι ⊕ ι → ℝ), ?_, ?_⟩
      · simp only [g, Sum.elim_inl] at this
        rw [hfx] at this
        show (Mᵀ *ᵥ _) j ≤ 0
        simpa [mulVec, dotProduct, mul_comm] using this
      · intro k; show (0:ℝ) ≤ (Pi.single (Sum.inl j) (1:ℝ) : ι ⊕ ι → ℝ) k
        by_cases h : k = Sum.inl j <;> simp [Pi.single_apply, h]
      · simp [Pi.single_apply]
    · rw [hfx] at hfq
      rw [dotProduct_comm] ; linarith
  · rintro ⟨u, hu, hMu, hq⟩
    ext z
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨hz, hw⟩
    have h1 : q ≤ M *ᵥ z := fun i => by have := hw i; simp only [Pi.sub_apply, Pi.zero_apply] at this ⊢; linarith
    have h3 : u ⬝ᵥ q ≤ u ⬝ᵥ (M *ᵥ z) := dotProduct_le_dotProduct_of_nonneg_left h1 hu
    have h4 : u ⬝ᵥ (M *ᵥ z) = (Mᵀ *ᵥ u) ⬝ᵥ z := by
      rw [dotProduct_mulVec, mulVec_transpose]
    have h5 : (Mᵀ *ᵥ u) ⬝ᵥ z ≤ 0 := by
      have := dotProduct_le_dotProduct_of_nonneg_right hMu hz
      simpa using this
    linarith

end LemkeLCP.Existence

open LemkeLCP.Existence


theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (q : ι → ℝ) :
    Z M q = ∅ ↔ ∃ u : ι → ℝ, 0 ≤ u ∧ Mᵀ *ᵥ u ≤ 0 ∧ 0 < u ⬝ᵥ q := by
  exact farkas_core M q
