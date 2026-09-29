-- Prove2me | solution 1 for ModularCurve.eq_zero_of_forall_sum_mul_taylorCoeff_mul_pow_eq_zero_of_generalPosition
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/151367cc-bf0a-5a17-9dc7-17727a65a7b7

import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff
import Theorems.Thm_ModularCurve_exists_eq_algebraMap_of_forall_taylorCoeff_mul_pow_eq_zero_of_generalPosition
import Theorems.Thm_AlgebraicCurve_Place_taylorCoeff_add
import Theorems.Thm_AlgebraicCurve_Place_taylorCoeff_smul
import Theorems.Thm_AlgebraicCurve_Place_taylorCoeff_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_eq_zero_of_forall_sum_mul_taylorCoeff_mul_pow_eq_zero_of_generalPosition
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve ModularCurve

namespace PolarMatrix

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_of_ord_nonneg' (w : Place K F) {f : F} (h : 0 ≤ w.ord f) : f ∈ w.toValuationSubring := by
  by_cases hf0 : f = 0
  · rw [hf0]; exact zero_mem _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow hf0 hπ
  rw [hu, ← Int.toNat_of_nonneg h, zpow_natCast]
  exact mul_mem (u : w.toValuationSubring).2 (pow_mem π.2 _)

theorem ne_zero_of_ord_eq_one (w : Place K F) {t : F} (ht : w.ord t = 1) : t ≠ 0 := by
  intro e
  rw [e, Place.ord_zero] at ht
  exact zero_ne_one ht

theorem smul_mem' (w : Place K F) (c : K) {f : F} (hf : f ∈ w.toValuationSubring) :
    c • f ∈ w.toValuationSubring := by
  rw [Algebra.smul_def]
  exact mul_mem (w.algebraMap_mem' c) hf

theorem mul_pow_mem (w : Place K F) {t : F} (ht : w.ord t = 1) (m : ℕ) {h : F}
    (hh : -(m : ℤ) ≤ w.ord h) : h * t ^ m ∈ w.toValuationSubring := by
  by_cases h0 : h = 0
  · rw [h0, zero_mul]; exact zero_mem _
  refine mem_of_ord_nonneg' w ?_
  rw [w.ord_mul h0 (pow_ne_zero _ (ne_zero_of_ord_eq_one w ht)), ← zpow_natCast, w.ord_zpow, ht,
    mul_one]
  omega

theorem neg_le_ord_of_mul_pow_mem (w : Place K F) {t : F} (ht : w.ord t = 1) (m : ℕ) {h : F}
    (hmem : h * t ^ m ∈ w.toValuationSubring) : -(m : ℤ) ≤ w.ord h := by
  by_cases h0 : h = 0
  · rw [h0, Place.ord_zero]; omega
  have h1 := w.ord_nonneg_of_mem hmem
  rw [w.ord_mul h0 (pow_ne_zero _ (ne_zero_of_ord_eq_one w ht)), ← zpow_natCast, w.ord_zpow, ht,
    mul_one] at h1
  omega

theorem hasValue_add {w : Place K F} {g g' : F} {a a' : K} (h : w.HasValue g a)
    (h' : w.HasValue g' a') : w.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : w.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

theorem hasValue_zero (w : Place K F) : w.HasValue (0 : F) 0 := by
  have h := Place.hasValue_algebraMap w (0 : K)
  rwa [map_zero] at h

theorem hasValue_smul {w : Place K F} {g : F} {a : K} (h : w.HasValue g a) (c : K) :
    w.HasValue (c • g) (c * a) := by
  rw [Algebra.smul_def]
  exact (Place.hasValue_algebraMap w c).mul h

theorem hasValue_sum {w : Place K F} {ι : Type*} (s : Finset ι) (f : ι → F) (a : ι → K)
    (h : ∀ i ∈ s, w.HasValue (f i) (a i)) : w.HasValue (∑ i ∈ s, f i) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasValue_zero w
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact hasValue_add (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem taylorCoeff_sum_smul (w : Place K F) (hw : w.IsRational) {t : F} (ht : w.ord t = 1)
    {ι : Type*} (s : Finset ι) (c : ι → K) (f : ι → F)
    (hf : ∀ i ∈ s, f i ∈ w.toValuationSubring) (r : ℕ) :
    Place.taylorCoeff w t r (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i * Place.taylorCoeff w t r (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, show (0 : F) = algebraMap K F 0 from (map_zero _).symm,
      Place.taylorCoeff_algebraMap]
    simp
  | insert i s hi ih =>
    have hfi : f i ∈ w.toValuationSubring := hf i (Finset.mem_insert_self i s)
    have hfs : ∀ j ∈ s, f j ∈ w.toValuationSubring := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hsmem : (∑ j ∈ s, c j • f j) ∈ w.toValuationSubring :=
      sum_mem fun j hj => smul_mem' w (c j) (hfs j hj)
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      Place.taylorCoeff_add w hw ht (smul_mem' w (c i) hfi) hsmem,
      Place.taylorCoeff_smul w hw ht hfi, ih hfs]

end PolarMatrix

open PolarMatrix in
theorem solution
    {k : Type*} [Field k] {N : ℕ} [NeZero N]
    (g : SemilinearAut k ↥(modularFunctionFieldC k N))
    (W E₁ E₂ : Finset (Place k ↥(modularFunctionFieldC k N)))
    (hgp₁ : ∀ h : ↥(modularFunctionFieldC k N),
      (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ E₁ → 0 ≤ v.ord h) → (∀ v ∈ E₁, -1 ≤ v.ord h) →
      (∀ w ∈ W, w.HasValue h 0) → h = 0)
    (hgp₂ : ∀ h : ↥(modularFunctionFieldC k N),
      (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ E₂ → 0 ≤ v.ord h) → (∀ v ∈ E₂, -1 ≤ v.ord h) →
      ∃ c : k, h = algebraMap k ↥(modularFunctionFieldC k N) c)
    (t : Place k ↥(modularFunctionFieldC k N) → ↥(modularFunctionFieldC k N))
    (ht₁ : ∀ v ∈ E₁, v.ord (t v) = 1) (ht₂ : ∀ v ∈ E₂, v.ord (t v) = 1)
    (hrat₁ : ∀ v ∈ E₁, v.IsRational) (hrat₂ : ∀ v ∈ E₂, v.IsRational)
    (m : ℕ) {n : ℕ} (b : Fin n → ↥(modularFunctionFieldC k N) × ↥(modularFunctionFieldC k N))
    (hb₁ : ∀ j, ∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ E₁ → 0 ≤ v.ord (b j).1)
    (hb₁' : ∀ j, ∀ v ∈ E₁, -(m : ℤ) ≤ v.ord (b j).1)
    (hb₂ : ∀ j, ∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ E₂ → 0 ≤ v.ord (b j).2)
    (hb₂' : ∀ j, ∀ v ∈ E₂, -(m : ℤ) ≤ v.ord (b j).2)
    (hbval : ∀ j, ∀ w ∈ W, ∃ c : k, w.HasValue (b j).1 c ∧ (g • w).HasValue (b j).2 c)
    (hind : ∀ (c : Fin n → k) (a : k),
      ∑ j, c j • (b j).1 = algebraMap k ↥(modularFunctionFieldC k N) a →
      ∑ j, c j • (b j).2 = algebraMap k ↥(modularFunctionFieldC k N) a → c = 0)
    (c : Fin n → k)
    (hc₁ : ∀ v ∈ E₁, ∀ r : ℕ, r + 1 < m →
      ∑ j, c j * Place.taylorCoeff v (t v) r ((b j).1 * t v ^ m) = 0)
    (hc₂ : ∀ v ∈ E₂, ∀ r : ℕ, r + 1 < m →
      ∑ j, c j * Place.taylorCoeff v (t v) r ((b j).2 * t v ^ m) = 0) :
    c = 0 := by
  classical
  set H₁ : ↥(modularFunctionFieldC k N) := ∑ j, c j • (b j).1 with hH₁
  set H₂ : ↥(modularFunctionFieldC k N) := ∑ j, c j • (b j).2 with hH₂

  have hH₁out : ∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ E₁ → 0 ≤ v.ord H₁ := fun v hv =>
    v.ord_nonneg_of_mem (sum_mem fun j _ => smul_mem' v (c j) (mem_of_ord_nonneg' v (hb₁ j v hv)))
  have hH₂out : ∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ E₂ → 0 ≤ v.ord H₂ := fun v hv =>
    v.ord_nonneg_of_mem (sum_mem fun j _ => smul_mem' v (c j) (mem_of_ord_nonneg' v (hb₂ j v hv)))
  have hmul₁ : ∀ v ∈ E₁, H₁ * t v ^ m = ∑ j, c j • ((b j).1 * t v ^ m) := fun v _ => by
    rw [hH₁, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => smul_mul_assoc (c j) (b j).1 (t v ^ m)
  have hmul₂ : ∀ v ∈ E₂, H₂ * t v ^ m = ∑ j, c j • ((b j).2 * t v ^ m) := fun v _ => by
    rw [hH₂, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => smul_mul_assoc (c j) (b j).2 (t v ^ m)
  have hH₁in : ∀ v ∈ E₁, -(m : ℤ) ≤ v.ord H₁ := fun v hv => by
    refine neg_le_ord_of_mul_pow_mem v (ht₁ v hv) m ?_
    rw [hmul₁ v hv]
    exact sum_mem fun j _ => smul_mem' v (c j) (mul_pow_mem v (ht₁ v hv) m (hb₁' j v hv))
  have hH₂in : ∀ v ∈ E₂, -(m : ℤ) ≤ v.ord H₂ := fun v hv => by
    refine neg_le_ord_of_mul_pow_mem v (ht₂ v hv) m ?_
    rw [hmul₂ v hv]
    exact sum_mem fun j _ => smul_mem' v (c j) (mul_pow_mem v (ht₂ v hv) m (hb₂' j v hv))
  have hHval : ∀ w ∈ W, ∃ a : k, w.HasValue H₁ a ∧ (g • w).HasValue H₂ a := by
    intro w hw
    choose a ha using fun j => hbval j w hw
    refine ⟨∑ j, c j * a j, ?_, ?_⟩
    · exact hasValue_sum _ _ _ fun j _ => hasValue_smul (ha j).1 (c j)
    · exact hasValue_sum _ _ _ fun j _ => hasValue_smul (ha j).2 (c j)
  have hpol₁ : ∀ v ∈ E₁, ∀ r : ℕ, r + 1 < m → Place.taylorCoeff v (t v) r (H₁ * t v ^ m) = 0 := by
    intro v hv r hr
    rw [hmul₁ v hv, taylorCoeff_sum_smul v (hrat₁ v hv) (ht₁ v hv) _ c _
      (fun j _ => mul_pow_mem v (ht₁ v hv) m (hb₁' j v hv)) r]
    exact hc₁ v hv r hr
  have hpol₂ : ∀ v ∈ E₂, ∀ r : ℕ, r + 1 < m → Place.taylorCoeff v (t v) r (H₂ * t v ^ m) = 0 := by
    intro v hv r hr
    rw [hmul₂ v hv, taylorCoeff_sum_smul v (hrat₂ v hv) (ht₂ v hv) _ c _
      (fun j _ => mul_pow_mem v (ht₂ v hv) m (hb₂' j v hv)) r]
    exact hc₂ v hv r hr
  obtain ⟨a, ha₁, ha₂⟩ :=
    exists_eq_algebraMap_of_forall_taylorCoeff_mul_pow_eq_zero_of_generalPosition g W E₁ E₂ hgp₁ hgp₂
      t ht₁ ht₂ hrat₁ hrat₂ m H₁ H₂ hH₁out hH₁in hH₂out hH₂in hHval hpol₁ hpol₂
  exact hind c a ha₁ ha₂

end S_ModularCurve_eq_zero_of_forall_sum_mul_taylorCoeff_mul_pow_eq_zero_of_generalPosition
end P2MW
export P2MW.S_ModularCurve_eq_zero_of_forall_sum_mul_taylorCoeff_mul_pow_eq_zero_of_generalPosition (solution)
