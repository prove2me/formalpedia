-- Prove2me | solution 1 for LinMaxLoad.theorem_7_km26_tail
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:58:21.579334+00:00
-- url     : https://prove2.me/submissions/ace7ee40-c6a1-4414-826d-79652719f7e1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LinMaxLoad_maxLoad
import Definitions.Def_LinMaxLoad_probLin
import Theorems.Thm_ListHashFurstenberg_Main_corollary_3_4

section
set_option autoImplicit false
namespace LinMaxLoad.Dev.Km26

theorem maxLoad_map {A A' B : Type*} [DecidableEq B] (e : A ≃ A') (g : A → B) (S : Finset A) :
    LinMaxLoad.maxLoad (g ∘ e.symm) (S.map e.toEmbedding) = LinMaxLoad.maxLoad g S := by
  unfold LinMaxLoad.maxLoad
  have h1 : (S.map e.toEmbedding).image (g ∘ e.symm) = S.image g := by
    ext b
    simp only [Finset.mem_image, Finset.mem_map_equiv, Function.comp]
    constructor
    · rintro ⟨a, ha, hb⟩
      exact ⟨e.symm a, by simpa using ha, hb⟩
    · rintro ⟨a, ha, hb⟩
      exact ⟨e a, by simpa using ha, by simpa using hb⟩
  rw [h1]
  apply Finset.sup_congr rfl
  intro b _
  rw [Finset.filter_map, Finset.card_map]
  congr 2
  ext a
  simp

noncomputable def hequiv (K E E' : Type*) [Field K] [AddCommGroup E] [Module K E]
    [AddCommGroup E'] [Module K E'] (r : ℕ) (e : E ≃ₗ[K] E') :
    (E →ₗ[K] (Fin r → K)) ≃ (E' →ₗ[K] (Fin r → K)) where
  toFun h := h ∘ₗ (e.symm : E' →ₗ[K] E)
  invFun h := h ∘ₗ (e : E →ₗ[K] E')
  left_inv h := by ext x; simp
  right_inv h := by ext x; simp

theorem avgLin_congr (K E E' : Type*) [Field K] [Fintype K] [AddCommGroup E] [Module K E]
    [Finite E] [AddCommGroup E'] [Module K E'] [Finite E'] (r : ℕ) (e : E ≃ₗ[K] E')
    (X : (E →ₗ[K] (Fin r → K)) → ℝ) :
    LinMaxLoad.avgLin K E r X =
      LinMaxLoad.avgLin K E' r (fun h => X ((hequiv K E E' r e).symm h)) := by
  unfold LinMaxLoad.avgLin
  letI : Fintype (E →ₗ[K] (Fin r → K)) := Fintype.ofFinite _
  letI : Fintype (E' →ₗ[K] (Fin r → K)) := Fintype.ofFinite _
  congr 1
  · exact Fintype.sum_equiv (hequiv K E E' r e) _ _ (fun h => by
      show X h = X ((hequiv K E E' r e).symm (hequiv K E E' r e h))
      rw [Equiv.symm_apply_apply])
  · exact congrArg _ (Fintype.card_congr (hequiv K E E' r e))

end LinMaxLoad.Dev.Km26

namespace LinMaxLoad
open LinMaxLoad.Dev.Km26 in
open Classical in
theorem chk_theorem_7_km26_tail {K E : Type*} [Field K] [Fintype K] [AddCommGroup E]
    [Module K E] [Finite E] (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hℓE : ℓ ≤ Module.finrank K E)
    (S : Finset E) (hSn : S.card < Fintype.card K ^ ℓ) (T : ℕ)
    (hT₀ : 8 * (Fintype.card K : ℝ) + 48 * (Fintype.card K : ℝ) * ℓ /
        Real.log ((Fintype.card K : ℝ) ^ ℓ / S.card) ≤ T)
    (hTm : T ≤ S.card) :
    probLin K E ℓ (fun h => T ≤ maxLoad (h : E → Fin ℓ → K) S) ≤
        9 * (S.card : ℝ) / ((Fintype.card K : ℝ) ^ ℓ * T) *
          Real.exp (24 * (Fintype.card K : ℝ) * ℓ / T) ∧
      9 * (S.card : ℝ) / ((Fintype.card K : ℝ) ^ ℓ * T) *
          Real.exp (24 * (Fintype.card K : ℝ) * ℓ / T) ≤
        9 * (S.card : ℝ) * Real.exp (Real.log ((Fintype.card K : ℝ) ^ ℓ / S.card) / 2) /
          ((Fintype.card K : ℝ) ^ ℓ * T) ∧
      9 * (S.card : ℝ) * Real.exp (Real.log ((Fintype.card K : ℝ) ^ ℓ / S.card) / 2) /
          ((Fintype.card K : ℝ) ^ ℓ * T) =
        9 / (T * Real.exp (Real.log ((Fintype.card K : ℝ) ^ ℓ / S.card) / 2)) := by
  set q : ℝ := (Fintype.card K : ℝ) with hq
  set m : ℕ := S.card with hm
  have hq2 : (2 : ℝ) ≤ q := by
    have := Fintype.one_lt_card (α := K)
    rw [hq]; exact_mod_cast this
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exfalso
      have hT : T = 0 := by omega
      rw [h] at hT₀
      simp [hT] at hT₀
      linarith
    · exact h
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hnR : (m : ℝ) < q ^ ℓ := by rw [hq]; exact_mod_cast hSn
  set L : ℝ := Real.log (q ^ ℓ / m) with hL
  have hLpos : 0 < L := Real.log_pos ((one_lt_div hmR).2 hnR)
  have hdiv : 0 ≤ 48 * q * ℓ / L := by positivity
  have hT8 : 8 * q ≤ (T : ℝ) := by linarith
  have hTpos : (0 : ℝ) < T := by linarith
  have hT48 : 48 * q * ℓ ≤ (T : ℝ) * L := by
    have h1 : 48 * q * ℓ / L ≤ T := by linarith
    rwa [div_le_iff₀ hLpos] at h1
  have hexp : 24 * q * ℓ / T ≤ L / 2 := by
    rw [div_le_iff₀ hTpos]; nlinarith
  have hnpos : (0 : ℝ) < q ^ ℓ := by positivity
  refine ⟨?_, ?_, ?_⟩
  · -- Cor 3.4
    set d := Module.finrank K E with hd
    haveI : Module.Finite K E := Module.Finite.of_finite
    let e : E ≃ₗ[K] (Fin d → K) := (Module.finBasis K E).equivFun
    have hc := ListHashFurstenberg.Main.corollary_3_4 (F := K) d ℓ hℓ hℓE (T : ℝ) hT8
      (S.map e.toEquiv.toEmbedding)
    have hprob : probLin K E ℓ (fun h => T ≤ maxLoad (h : E → Fin ℓ → K) S) =
        probLin K (Fin d → K) ℓ (fun h => (T : ℝ) ≤ (maxLoad h (S.map e.toEquiv.toEmbedding) : ℝ)) := by
      unfold probLin
      rw [avgLin_congr K E (Fin d → K) ℓ e]
      congr 1
      funext h
      have : maxLoad (((hequiv K E (Fin d → K) ℓ e).symm h : E →ₗ[K] (Fin ℓ → K)) : E → Fin ℓ → K) S
          = maxLoad (h : (Fin d → K) → Fin ℓ → K) (S.map e.toEquiv.toEmbedding) := by
        rw [← maxLoad_map e.toEquiv]
        congr 1
        funext x
        simp [hequiv]
      simp only [this, Nat.cast_le]
    rw [hprob]
    refine hc.trans ?_
    rw [Finset.card_map]
    have hceil : ⌈Real.logb (Fintype.card K) (T : ℝ)⌉₊ ≤ ℓ := by
      rw [Nat.ceil_le]
      rw [Real.logb_le_iff_le_rpow (by linarith) hTpos, Real.rpow_natCast]
      have : (T : ℝ) ≤ m := by exact_mod_cast hTm
      linarith
    have hnum : 8 * q * ((ℓ + 2 * ⌈Real.logb (Fintype.card K) (T : ℝ)⌉₊ : ℕ) : ℝ) / T ≤
        24 * q * ℓ / T := by
      apply div_le_div_of_nonneg_right _ hTpos.le
      have : ((ℓ + 2 * ⌈Real.logb (Fintype.card K) (T : ℝ)⌉₊ : ℕ) : ℝ) ≤ 3 * ℓ := by
        have : ℓ + 2 * ⌈Real.logb (Fintype.card K) (T : ℝ)⌉₊ ≤ 3 * ℓ := by omega
        exact_mod_cast this
      nlinarith
    have hpos : 0 ≤ 9 * (m : ℝ) / (q ^ ℓ * T) := by positivity
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hnum) hpos
  · have hpos : 0 ≤ 9 * (m : ℝ) / (q ^ ℓ * T) := by positivity
    calc 9 * (m : ℝ) / (q ^ ℓ * T) * Real.exp (24 * q * ℓ / T)
        ≤ 9 * (m : ℝ) / (q ^ ℓ * T) * Real.exp (L / 2) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hexp) hpos
      _ = 9 * (m : ℝ) * Real.exp (L / 2) / (q ^ ℓ * T) := by ring
  · have hx : Real.exp (L / 2) * Real.exp (L / 2) = q ^ ℓ / m := by
      rw [← Real.exp_add, add_halves, hL, Real.exp_log (by positivity)]
    have hxp : 0 < Real.exp (L / 2) := Real.exp_pos _
    field_simp
    have : (m : ℝ) * (Real.exp (L / 2) * Real.exp (L / 2)) = q ^ ℓ := by
      rw [hx]; field_simp
    nlinarith [this]
end LinMaxLoad
end

theorem solution : type_of% @LinMaxLoad.chk_theorem_7_km26_tail := @LinMaxLoad.chk_theorem_7_km26_tail
