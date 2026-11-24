-- Prove2me | solution 1 for GlobalTheory.gram_posSemidef_of_int_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:59:13.181113+00:00
-- url     : https://prove2.me/submissions/a1360767-17a0-4b4e-8ceb-622f158e45df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GramPosSemidefOfIntForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix
namespace GlobalTheory
theorem _root_.solution {X : Type} [AddCommGroup X] {r : ℕ}
    (b : LinearMap.BilinForm ℤ X) (hsymm : ∀ y z, b y z = b z y) (hpos : ∀ y, 0 ≤ b y y)
    (v : Fin r → X) : (Matrix.of fun i j => (b (v i) (v j) : ℝ)).PosSemidef := by
  set G : Matrix (Fin r) (Fin r) ℝ := Matrix.of fun i j => (b (v i) (v j) : ℝ) with hG
  have hint : ∀ m : Fin r → ℤ, 0 ≤ ∑ i, ∑ j, (m i : ℝ) * (m j : ℝ) * G i j := by
    intro m
    have key : (∑ i, ∑ j, m i * m j * b (v i) (v j) : ℤ)
        = b (∑ i, m i • v i) (∑ j, m j • v j) := by
      simp only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply, smul_eq_mul,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hsymm (v i) (v j)]; ring
    have h0 : (0:ℝ) ≤ ((∑ i, ∑ j, m i * m j * b (v i) (v j) : ℤ) : ℝ) := by
      rw [key]; exact_mod_cast hpos _
    simpa [hG] using h0
  have hrat : ∀ c : Fin r → ℚ, 0 ≤ ∑ i, ∑ j, (c i : ℝ) * (c j : ℝ) * G i j := by
    intro c
    set N : ℕ := ∏ i, (c i).den with hN
    have hNpos : (0:ℝ) < N := by
      have : 0 < N := Finset.prod_pos (fun i _ => (c i).den_pos)
      exact_mod_cast this
    have hm : ∀ i, ∃ k : ℤ, (k : ℝ) = N * (c i : ℝ) := by
      intro i
      obtain ⟨t, ht⟩ : (c i).den ∣ N := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      refine ⟨(c i).num * t, ?_⟩
      have h1 : ((c i).num : ℚ) = c i * (c i).den := (Rat.mul_den_eq_num (c i)).symm
      have h2 : ((c i).num : ℝ) = (c i : ℝ) * (c i).den := by exact_mod_cast h1
      rw [ht]; push_cast
      rw [h2]; ring
    choose m hm using hm
    have h3 := hint m
    simp_rw [hm] at h3
    have e : ∑ i, ∑ j, ((N:ℝ) * c i) * (N * c j) * G i j
        = (N:ℝ) ^ 2 * ∑ i, ∑ j, (c i : ℝ) * (c j : ℝ) * G i j := by
      simp_rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e] at h3
    exact (mul_nonneg_iff_of_pos_left (by positivity)).mp h3
  have hreal : ∀ x : Fin r → ℝ, 0 ≤ ∑ i, ∑ j, x i * x j * G i j := by
    intro x
    have hd : DenseRange (Pi.map fun (_ : Fin r) (q : ℚ) => (q : ℝ)) :=
      DenseRange.piMap fun _ => Rat.denseRange_cast
    refine hd.induction_on (p := fun x : Fin r → ℝ => 0 ≤ ∑ i, ∑ j, x i * x j * G i j) x ?_ ?_
    · exact isClosed_le continuous_const (by fun_prop)
    · intro c
      simpa [Pi.map] using hrat c
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    simp [hG, Matrix.conjTranspose_apply, hsymm]
  · intro x
    have e : star x ⬝ᵥ (G *ᵥ x) = ∑ i, ∑ j, x i * x j * G i j := by
      simp only [dotProduct, mulVec, star_trivial, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e]; exact hreal x
end GlobalTheory
