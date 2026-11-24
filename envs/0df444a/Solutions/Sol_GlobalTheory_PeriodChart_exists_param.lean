-- Prove2me | solution 1 for GlobalTheory.PeriodChart.exists_param
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:24:33.000054+00:00
-- url     : https://prove2.me/submissions/564003bd-fe2c-4874-a861-630a7f910ba0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsContraction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodChart
namespace GlobalTheory.PeriodChart
theorem _root_.solution {ι : Type} [Fintype ι] (R : ι → ι → Prop) (s : ι → Prop) (hR : ∀ i j, R i j → R j i)
    (hs : ∀ i j, R i j → (s i ↔ ¬ s j)) :
    ∃ (m : ℕ) (L : (Fin m → ℂ) →ₗ[ℂ] Matrix ι ι ℂ), 2 * m = Nat.card {x : ι × ι // R x.1 x.2} ∧
      Function.Injective L ∧ ∀ W : Matrix ι ι ℂ, (∃ b, L b = W) ↔ Wᵀ = W ∧ ∀ i j, ¬ R i j → W i j = 0 := by
  classical

  obtain ⟨e⟩ : Nonempty ({x : ι × ι // R x.1 x.2 ∧ s x.1} ≃ Fin (Nat.card {x : ι × ι // R x.1 x.2 ∧ s x.1})) :=
    ⟨Finite.equivFin _⟩
  have hflip : ∀ i j, R i j → ¬ s i → s j := fun i j hr hsi =>
    not_not.mp (mt (hs i j hr).mpr hsi)
  refine ⟨Nat.card {x : ι × ι // R x.1 x.2 ∧ s x.1},
    { toFun := fun b => Matrix.of fun i j =>
        if h : R i j ∧ s i then b (e ⟨(i, j), h⟩)
        else if h' : R j i ∧ s j then b (e ⟨(j, i), h'⟩) else 0
      map_add' := fun b b' => by
        ext i j
        simp only [Matrix.add_apply, Matrix.of_apply]
        split_ifs <;> simp
      map_smul' := fun c b => by
        ext i j
        simp only [Matrix.smul_apply, Matrix.of_apply, RingHom.id_apply]
        split_ifs <;> simp }, ?_, ?_, ?_⟩
  ·
    have eqv : {x : ι × ι // R x.1 x.2} ≃
        {x : ι × ι // R x.1 x.2 ∧ s x.1} ⊕ {x : ι × ι // R x.1 x.2 ∧ s x.1} :=
      { toFun := fun x => if h : s x.1.1 then Sum.inl ⟨x.1, x.2, h⟩
          else Sum.inr ⟨x.1.swap, hR _ _ x.2, hflip _ _ x.2 h⟩
        invFun := Sum.elim (fun k => ⟨k.1, k.2.1⟩) (fun k => ⟨k.1.swap, hR _ _ k.2.1⟩)
        left_inv := by
          rintro ⟨⟨i, j⟩, hr⟩
          by_cases h : s i <;> simp [h]
        right_inv := by
          rintro (⟨⟨i, j⟩, hr, hsi⟩ | ⟨⟨i, j⟩, hr, hsi⟩)
          · simp [hsi]
          · have : ¬ s j := (hs i j hr).mp hsi
            simp [this] }
    rw [Nat.card_congr eqv, Nat.card_sum]
    ring
  · intro b b' hbb
    funext n
    obtain ⟨⟨⟨i, j⟩, hr, hsi⟩, rfl⟩ := e.surjective n
    have := congrFun (congrFun hbb i) j
    simpa [Matrix.of_apply, hr, hsi] using this
  · intro W
    constructor
    · rintro ⟨b, rfl⟩
      refine ⟨?_, ?_⟩
      · ext i j
        simp only [Matrix.transpose_apply, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply]
        by_cases h1 : R i j ∧ s i
        · have h2 : ¬ (R j i ∧ s j) := fun h => (hs _ _ h1.1).mp h1.2 h.2
          simp only [dif_pos h1, dif_neg h2]
        · by_cases h2 : R j i ∧ s j
          · simp only [dif_pos h2, dif_neg h1]
          · simp only [dif_neg h1, dif_neg h2]
      · intro i j hij
        simp only [LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply]
        rw [dif_neg (fun h : R i j ∧ s i => hij h.1), dif_neg (fun h : R j i ∧ s j => hij (hR _ _ h.1))]
    · rintro ⟨hW, hz⟩
      refine ⟨fun n => W (e.symm n).1.1 (e.symm n).1.2, ?_⟩
      ext i j
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply]
      by_cases h1 : R i j ∧ s i
      · rw [dif_pos h1, Equiv.symm_apply_apply]
      · by_cases h2 : R j i ∧ s j
        · rw [dif_neg h1, dif_pos h2, Equiv.symm_apply_apply]
          simpa using congrFun (congrFun hW i) j
        · rw [dif_neg h1, dif_neg h2]
          refine (hz i j fun hr => ?_).symm
          by_cases hsi : s i
          · exact h1 ⟨hr, hsi⟩
          · exact h2 ⟨hR _ _ hr, hflip _ _ hr hsi⟩
end GlobalTheory.PeriodChart
