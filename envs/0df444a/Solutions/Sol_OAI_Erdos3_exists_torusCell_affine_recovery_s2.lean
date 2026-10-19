-- Prove2me | solution 1 for OAI.Erdos3.exists_torusCell_affine_recovery_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T10:47:45.117563+00:00
-- url     : https://prove2.me/submissions/16c9059f-dbe2-484b-8402-1e0b651996c1

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B100

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerLiftOffset
namespace OAI

section

namespace Erdos3

theorem integer_lift_offset_eq {d m : ℕ} (M : Fin m → Fin d → ℤ) (a : Fin d → ℝ)
    (x x' : Fin d → ℝ) (k k' : Fin d → ℤ) (β β' : Fin m → ℤ) {K r : ℝ}
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) (hr : 0 ≤ r) (hgap : 2 * K * r + 1 / 2 < 1)
    (hx : ∀ j, |x j - (k j : ℝ) - a j| ≤ r)
    (hx' : ∀ j, |x' j - (k' j : ℝ) - a j| ≤ r)
    (hβ : ∀ i, |(∑ j, (M i j : ℝ) * x j) - β i| ≤ 1 / 4)
    (hβ' : ∀ i, |(∑ j, (M i j : ℝ) * x' j) - β' i| ≤ 1 / 4) :
    (fun i => β i - ∑ j, M i j * k j) = fun i => β' i - ∑ j, M i j * k' j := by
  funext i
  have herr (j : Fin d) :
      |(x j - (k j : ℝ) - a j) - (x' j - (k' j : ℝ) - a j)| ≤ 2 * r :=
    (abs_sub _ _).trans (by linarith [hx j, hx' j])
  have hsum : |∑ j, (M i j : ℝ) *
      ((x j - (k j : ℝ) - a j) - (x' j - (k' j : ℝ) - a j))| ≤ K * (2 * r) := by
    calc
      _ ≤ ∑ j, |(M i j : ℝ) *
          ((x j - (k j : ℝ) - a j) - (x' j - (k' j : ℝ) - a j))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |(M i j : ℝ)| * (2 * r) := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (herr j) (abs_nonneg _)
      _ = (∑ j, |(M i j : ℝ)|) * (2 * r) := (Finset.sum_mul _ _ _).symm
      _ ≤ K * (2 * r) := mul_le_mul_of_nonneg_right (hM i) (by positivity)
  have hlifts : |((∑ j, (M i j : ℝ) * x j) - β i) -
      ((∑ j, (M i j : ℝ) * x' j) - β' i)| ≤ 1 / 2 :=
    (abs_sub _ _).trans (by linarith [hβ i, hβ' i])
  have hid : (((β i - ∑ j, M i j * k j) - (β' i - ∑ j, M i j * k' j) : ℤ) : ℝ) =
      (∑ j, (M i j : ℝ) *
        ((x j - (k j : ℝ) - a j) - (x' j - (k' j : ℝ) - a j))) -
      (((∑ j, (M i j : ℝ) * x j) - β i) - ((∑ j, (M i j : ℝ) * x' j) - β' i)) := by
    push_cast
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  have hbound := (abs_sub _ _).trans (add_le_add hsum hlifts)
  rw [← hid] at hbound
  have habs : |(((β i - ∑ j, M i j * k j) - (β' i - ∑ j, M i j * k' j) : ℤ) : ℝ)| < 1 :=
    hbound.trans_lt (by nlinarith [hgap])
  have hlo : (-1 : ℤ) < (β i - ∑ j, M i j * k j) - (β' i - ∑ j, M i j * k' j) := by
    exact_mod_cast (abs_lt.mp habs).1
  have hhi : (β i - ∑ j, M i j * k j) - (β' i - ∑ j, M i j * k' j) < (1 : ℤ) := by
    exact_mod_cast (abs_lt.mp habs).2
  omega

theorem exists_integer_lift_offset {Ω : Type*} {d m : ℕ} (S : Set Ω)
    (M : Fin m → Fin d → ℤ) (a : Fin d → ℝ) (x : Ω → Fin d → ℝ)
    (k : Ω → Fin d → ℤ) (β : Ω → Fin m → ℤ) {K r : ℝ}
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) (hr : 0 ≤ r) (hgap : 2 * K * r + 1 / 2 < 1)
    (hx : ∀ u ∈ S, ∀ j, |x u j - (k u j : ℝ) - a j| ≤ r)
    (hβ : ∀ u ∈ S, ∀ i, |(∑ j, (M i j : ℝ) * x u j) - β u i| ≤ 1 / 4) :
    ∃ c : Fin m → ℤ, ∀ u ∈ S, β u = fun i => c i + ∑ j, M i j * k u j := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨v, hv⟩ := hS
    refine ⟨fun i => β v i - ∑ j, M i j * k v j, ?_⟩
    intro u hu
    have heq := integer_lift_offset_eq M a (x u) (x v) (k u) (k v) (β u) (β v)
      hM hr hgap (hx u hu) (hx v hv) (hβ u hu) (hβ v hv)
    funext i
    have hi := congrFun heq i
    dsimp only at hi ⊢
    omega
  · exact ⟨0, fun u hu => (hS ⟨u, hu⟩).elim⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedParameterPatchRankPadding
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem localTentKernel_support {d q : ℕ} (hq : 8 ≤ q) (x : Fin d → ℝ)
    (hx : (localTentKernel d q hq).value x ≠ 0) : dist x 0 ≤ 2 / (q : ℝ) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  apply (le_div_iff₀ hqR).mpr
  have hsmall : (q : ℝ) / 2 * dist x 0 < 1 := by
    by_contra h
    exact hx (max_eq_left (by linarith))
  nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.TorusCellBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem torusGridKernel_support (d q : ℕ) (hq : 8 ≤ q) (a : Fin d → Fin q)
    (x : Fin d → ℝ) (hx : (torusGridKernel d q hq a).value x ≠ 0) :
    dist x 0 ≤ 2 / (q : ℝ) := by
  apply localTentKernel_support hq
  intro h
  apply hx
  change (localTentKernel d q hq).value x / _ = 0
  rw [h, zero_div]

end Erdos3

end

section

namespace Erdos3

theorem exists_torusCell_lift_offset {Ω : Type*} {d m q : ℕ}
    (hq : 8 ≤ q) (S : Set Ω) (M : Fin m → Fin d → ℤ) (a : Fin d → Fin q)
    (x : Ω → Fin d → ℝ) (k : Ω → Fin d → ℤ) (β : Ω → Fin m → ℤ) {K : ℝ}
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) (hmesh : 16 * K ≤ (q : ℝ))
    (hcell : ∀ u ∈ S, (torusGridKernel d q hq a).value
      (fun j => (k u j : ℝ) - (x u - torusGridCenter q a) j) ≠ 0)
    (hβ : ∀ u ∈ S, ∀ i, |(∑ j, (M i j : ℝ) * x u j) - β u i| ≤ 1 / 4) :
    ∃ c : Fin m → ℤ, ∀ u ∈ S, β u = fun i => c i + ∑ j, M i j * k u j := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  apply exists_integer_lift_offset S M (torusGridCenter q a) x k β hM
    (r := 2 / (q : ℝ)) (by positivity) _ _ hβ
  · have hsmall : 4 * K / (q : ℝ) ≤ 1 / 4 :=
      (div_le_iff₀ hqR).mpr (by linarith)
    calc
      2 * K * (2 / (q : ℝ)) + 1 / 2 = 4 * K / (q : ℝ) + 1 / 2 := by ring
      _ < 1 := by linarith
  · intro u hu j
    have h := torusGridKernel_support d q hq a _ (hcell u hu)
    have hc := (dist_le_pi_dist (fun j => (k u j : ℝ) - (x u - torusGridCenter q a) j) 0 j).trans h
    simp only [Real.dist_eq, Pi.zero_apply, sub_zero, Pi.sub_apply] at hc
    have heq : x u j - (k u j : ℝ) - torusGridCenter q a j =
        -((k u j : ℝ) - (x u j - torusGridCenter q a j)) := by ring
    simpa only [heq, abs_neg] using hc

end Erdos3

end

section

namespace Erdos3

namespace PatchKernel

variable {d : ℕ}

theorem periodicValue_eq_integerLift (Φ : PatchKernel d) (x : Fin d → ℝ) :
    Φ.periodicValue x = Φ.value (fun j => (Φ.integerLift x j : ℝ) - x j) := by
  classical
  by_cases h : ∃ b : Fin d → ℤ, Φ.value (fun j => (b j : ℝ) - x j) ≠ 0
  · simp only [integerLift, dif_pos h]
    exact (constantSlots x).patchValue_eq_of_nonzero Φ h.choose_spec
  · have hz : ∀ b : Fin d → ℤ, Φ.value (fun j => (b j : ℝ) - x j) = 0 := by simpa using h
    have hp : Φ.periodicValue x = 0 := (constantSlots x).patchValue_eq_zero Φ hz
    simpa only [integerLift, dif_neg h, hz] using hp

theorem integerLift_contributes (Φ : PatchKernel d) (x : Fin d → ℝ)
    (hx : Φ.periodicValue x ≠ 0) : Φ.value (fun j => (Φ.integerLift x j : ℝ) - x j) ≠ 0 := by
  rwa [← Φ.periodicValue_eq_integerLift x]

end PatchKernel

theorem exists_torusCell_affine_recovery_s2_oai {Ω : Type*} {d m q : ℕ}
    (hq : 8 ≤ q) (S : Set Ω) (M : Fin m → Fin d → ℤ) (a : Fin d → Fin q)
    (x : Ω → Fin d → ℝ) (β : Ω → Fin m → ℤ) {K : ℝ}
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) (hmesh : 16 * K ≤ (q : ℝ))
    (hactive : ∀ u ∈ S, (torusGridKernel d q hq a).periodicValue (x u - torusGridCenter q a) ≠ 0)
    (hβ : ∀ u ∈ S, ∀ i, |(∑ j, (M i j : ℝ) * x u j) - β u i| ≤ 1 / 4) :
    ∃ c : Fin m → ℤ, ∀ u ∈ S, β u = fun i => c i + ∑ j, M i j *
      (torusGridKernel d q hq a).integerLift (x u - torusGridCenter q a) j := by
  apply exists_torusCell_lift_offset hq S M a x
    (fun u => (torusGridKernel d q hq a).integerLift (x u - torusGridCenter q a)) β hM hmesh
  · intro u hu
    exact (torusGridKernel d q hq a).integerLift_contributes _ (hactive u hu)
  · exact hβ

end Erdos3

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Erdos3.exists_torusCell_affine_recovery_s2_oai.{u_1} := @OAI.Erdos3.exists_torusCell_affine_recovery_s2_oai.{u_1}
