-- Prove2me | solution 1 for GlobalTheory.exists_weierstrassP_mul_eq_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:12:45.782575+00:00
-- url     : https://prove2.me/submissions/9c36a8db-bb14-471b-af24-5da8a505d658

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNumeratorOfInvolution
import Theorems.Thm_GlobalTheory_exists_numerator_of_involution
import Theorems.Thm_GlobalTheory_weierstrassP_mul_eq_sum
import Theorems.Thm_GlobalTheory_exists_representatives
import Theorems.Thm_GlobalTheory_derivWeierstrassP_eq_zero_iff
import Theorems.Thm_GlobalTheory_latticePointEquiv_mk
import Theorems.Thm_GlobalTheory_weierstrassP_add_add_sub
import Theorems.Thm_GlobalTheory_weierstrassP_eq_iff
import Theorems.Thm_GlobalTheory_weierstrassP_second_ne_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.latticePointEquiv_mk



set_option autoImplicit false
open Filter PeriodPair Polynomial
open scoped Topology
noncomputable section
open GlobalTheory
variable {L L' : PeriodPair} {α : ℂ}
namespace GlobalTheory
theorem _root_.solution (hα0 : α ≠ 0) (hα : ∀ l ∈ L.lattice, α * l ∈ L'.lattice)
    (k : Subfield ℂ) (h₂ : L.g₂ ∈ k) (h₃ : L.g₃ ∈ k) (hαk : α ∈ k)
    (hk : ∀ t ∉ L.lattice, α * t ∈ L'.lattice → ℘[L] t ∈ k) :
    ∃ A D : ℂ[X], (∀ i, A.coeff i ∈ k) ∧ (∀ i, D.coeff i ∈ k) ∧ D.Monic ∧
      A.leadingCoeff = (α ^ 2)⁻¹ ∧ IsCoprime A D ∧
      A.natDegree = (L.lattice.toAddSubgroup.map (AddMonoidHom.mulLeft α)).relIndex
        L'.lattice.toAddSubgroup ∧
      D.natDegree + 1 = A.natDegree ∧
      (∀ z ∉ L.lattice, D.eval (℘[L] z) = 0 ↔ α * z ∈ L'.lattice) ∧
      ∀ z, α * z ∉ L'.lattice → ℘[L'] (α * z) = A.eval (℘[L] z) / D.eval (℘[L] z) := by
  classical
  obtain ⟨Q, _, _, r, hc, r1, r2, r3, r4, r5⟩ := exists_representatives hα0 hα
  have := Fintype.ofFinite Q
  let ι := {t : Q // t ≠ 0}
  have hr : ∀ t : ι, r t ∉ L.lattice := fun t ↦ (r4 t).not.mpr t.2
  let σ : ι → ι := fun t ↦ ⟨-t, neg_ne_zero.mpr t.2⟩
  have hneg : ∀ t : Q, ∃ l : L.lattice, r (-t) = -r t + l := fun t ↦
    ⟨⟨_, (r3 (-t) t).mpr rfl⟩, by simp⟩
  have hC : ∀ c ∈ k, C c ∈ liftsRing k.subtype := fun c hc ↦ C'_mem_lifts ⟨⟨c, hc⟩, rfl⟩
  have hpk : ∀ t : ι, ℘[L] (r t) ∈ k := fun t ↦ hk _ (hr t) (r1 t)
  have hn : ∀ n : ℕ, (n : ℂ) ∈ k := fun n ↦ natCast_mem k n
  obtain ⟨A, hAk, hAm, hAd, hAc, hAe⟩ := exists_numerator_of_involution σ
    (fun t ↦ Subtype.ext (neg_neg _)) (fun t ↦ ℘[L] (r t))
    (fun t ↦ (6 * ℘[L] (r t) ^ 2 - L.g₂ / 2) / 2) (fun t ↦ ℘'[L] (r t) ^ 2 / 2)
    (fun s t ↦ by
      rw [weierstrassP_eq_iff L (hr s) (hr t), r2, r3, Subtype.ext_iff, Subtype.ext_iff])
    (fun t ↦ by obtain ⟨l, hl⟩ := hneg t; simp [σ, hl])
    (fun t ↦ by
      rw [Subtype.ext_iff, eq_comm (b := t.1), ← r3, ← derivWeierstrassP_eq_zero_iff L (hr t)]
      simp)
    (fun t ht ↦ div_ne_zero (weierstrassP_second_ne_zero L (hr t) (by
      rwa [Subtype.ext_iff, eq_comm (b := t.1), ← r3,
        ← derivWeierstrassP_eq_zero_iff L (hr t)] at ht)) two_ne_zero)
    (liftsRing k.subtype) (X_mem_lifts _) (fun t ↦ ⟨hC _ (hpk t),
      hC _ (div_mem (sub_mem (mul_mem (hn 6) (pow_mem (hpk t) 2)) (div_mem h₂ (hn 2))) (hn 2)),
      hC _ (div_mem (by
        rw [L.derivWeierstrassP_sq _ (hr t)]
        exact sub_mem (sub_mem (mul_mem (hn 4) (pow_mem (hpk t) 3)) (mul_mem h₂ (hpk t))) h₃)
        (hn 2))⟩)
  have hcoeff : ∀ P ∈ liftsRing k.subtype, ∀ i, P.coeff i ∈ k := fun P hP i ↦ by
    obtain ⟨c, hc⟩ := (lifts_iff_coeff_lifts P).mp hP i
    exact hc ▸ c.2
  have hα2 : (α ^ 2)⁻¹ ≠ 0 := by simp [hα0]
  have hcard : Fintype.card ι + 1 = Nat.card Q := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      Nat.sub_add_cancel Fintype.card_pos]
  have hD0 : ∀ z ∉ L.lattice, (∃ t : ι, ℘[L] z = ℘[L] (r t)) ↔ α * z ∈ L'.lattice := fun z hz ↦ by
    constructor
    · rintro ⟨t, ht⟩
      rcases (weierstrassP_eq_iff L hz (hr t)).mp ht with h | h
      · simpa [mul_sub] using add_mem (hα _ h) (r1 t)
      · simpa [mul_add] using sub_mem (hα _ h) (r1 t)
    · intro h
      obtain ⟨t, ht⟩ := r5 z h
      have ht0 : t ≠ 0 := fun e ↦ hz (by simpa using add_mem ht ((r4 t).mpr e))
      exact ⟨⟨t, ht0⟩, (weierstrassP_eq_iff L hz (hr ⟨t, ht0⟩)).mpr (.inl ht)⟩
  refine ⟨C (α ^ 2)⁻¹ * A, ∏ t : ι, (X - C (℘[L] (r t))),
    hcoeff _ (mul_mem (hC _ (inv_mem (pow_mem hαk 2))) hAk),
    hcoeff _ (prod_mem fun t _ ↦ sub_mem (X_mem_lifts _) (hC _ (hpk t))),
    monic_prod_of_monic _ _ fun t _ ↦ monic_X_sub_C _, by simp [hAm],
    (isCoprime_mul_unit_left_left (isUnit_C.mpr hα2.isUnit) _ _).mpr hAc,
    by rw [natDegree_C_mul hα2, hAd, hcard, hc], ?_, fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rw [natDegree_C_mul hα2, hAd, natDegree_prod_of_monic _ _ fun t _ ↦ monic_X_sub_C _]
    simp
  · rw [← hD0 z hz]
    simp [eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero]
  · have hzL : z ∉ L.lattice := fun h ↦ hz (hα z h)
    have hx : ∀ t : ι, ℘[L] z ≠ ℘[L] (r t) := fun t h ↦ hz ((hD0 z hzL).mp ⟨t, h⟩)
    have hP : ∏ t : ι, (℘[L] z - ℘[L] (r t)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun t _ ↦ sub_ne_zero.mpr (hx t)
    have s1 := weierstrassP_mul_eq_sum hα0 hα r r1 (fun s t ↦ (r2 s t).mp) r5 z
    have s2 : α ^ 2 * ℘[L'] (α * z) = ∑ t, (℘[L] (z + r t) - ℘[L] (r t)) := by
      rw [s1]
      refine (Fintype.sum_equiv (Equiv.neg Q) _ _ fun t ↦ ?_).symm
      obtain ⟨l, hl⟩ := hneg t
      simp [hl, ← sub_sub]
    have s3 : 2 * (α ^ 2 * ℘[L'] (α * z)) =
        ∑ t, (℘[L] (z + r t) + ℘[L] (z - r t) - 2 * ℘[L] (r t)) := by
      rw [two_mul]
      nth_rw 1 [s1]
      rw [s2, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun t _ ↦ by ring
    have h0 := (r4 0).mpr rfl
    rw [Fintype.sum_eq_add_sum_subtype_ne _ 0, L.weierstrassP_add_coe z ⟨_, h0⟩,
      L.weierstrassP_sub_coe z ⟨_, h0⟩, L.weierstrassP_coe ⟨_, h0⟩,
      Finset.sum_congr rfl fun (t : ι) _ ↦ weierstrassP_add_add_sub L hzL (hr t) (hx t)] at s3
    have s4 : ∑ t : ι, ((6 * ℘[L] (r t) ^ 2 - L.g₂ / 2) / (℘[L] z - ℘[L] (r t)) +
        ℘'[L] (r t) ^ 2 / (℘[L] z - ℘[L] (r t)) ^ 2) =
        2 * ∑ t : ι, ((6 * ℘[L] (r t) ^ 2 - L.g₂ / 2) / 2 / (℘[L] z - ℘[L] (r t)) +
        ℘'[L] (r t) ^ 2 / 2 / (℘[L] z - ℘[L] (r t)) ^ 2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun t _ ↦ by ring
    rw [s4] at s3
    rw [eval_mul, eval_C, hAe _ hx, eval_prod]
    simp only [eval_sub, eval_X, eval_C]
    rw [mul_div_assoc, mul_div_cancel_left₀ _ hP, eq_inv_mul_iff_mul_eq₀ (pow_ne_zero 2 hα0)]
    linear_combination s3 / 2
end GlobalTheory
