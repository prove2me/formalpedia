-- Prove2me | solution 1 for MultitaskContracts.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-20T01:11:30.41287+00:00
-- url     : https://prove2.me/submissions/efc82122-e31d-4bd1-a7f2-6b6b1534ce50

import Mathlib
import Definitions.Def_MultitaskContracts_Instance
import Definitions.Def_MultitaskContracts_bundle
import Definitions.Def_MultitaskContracts_separable
import Definitions.Def_MultitaskContracts_priceOfSeparation
import Definitions.Def_MultitaskContracts_Instance_IsIndependent

set_option autoImplicit false

namespace MultitaskContracts_Theorem2_Proof

open MultitaskContracts
open scoped ENNReal

/-! ### Part 1: Combinatorial Sum & Product Identities over `Finset K` -/

section Combinatorics

variable {K : Type*} [Fintype K] [DecidableEq K]

lemma prod_ite_mem_eq (s Y : Finset K) (hY : Y ⊆ s) (f g : K → ℝ) :
    (∏ j ∈ s, if j ∈ Y then f j else g j) =
      (∏ j ∈ Y, f j) * (∏ j ∈ s \ Y, g j) := by
  rw [Finset.prod_ite]
  congr 1
  · congr 1
    ext j
    simp only [Finset.mem_filter, and_iff_right_iff_imp]
    intro hj
    exact hY hj
  · congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_sdiff]

lemma sum_powerset_prod_ite (s : Finset K) (r : K → ℝ) :
    (∑ Y ∈ s.powerset, ∏ j ∈ s, (if j ∈ Y then r j else 1 - r j)) = 1 := by
  have hcongr :
      (∑ Y ∈ s.powerset, ∏ j ∈ s, (if j ∈ Y then r j else 1 - r j)) =
        ∑ Y ∈ s.powerset, (∏ j ∈ Y, r j) * (∏ j ∈ s \ Y, (1 - r j)) := by
    refine Finset.sum_congr rfl ?_
    intro Y hY
    exact prod_ite_mem_eq s Y (Finset.mem_powerset.mp hY) r (fun j => 1 - r j)
  rw [hcongr, ← Finset.prod_add]
  simp

lemma mem_powerset_erase_univ_iff (k : K) (Y : Finset K) :
    Y ∈ (Finset.univ.erase k).powerset ↔ k ∉ Y := by
  rw [Finset.mem_powerset]
  constructor
  · intro h hk
    exact Finset.notMem_erase k Finset.univ (h hk)
  · intro hk x hx
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ x⟩
    rintro rfl
    exact hk hx

lemma sum_filter_mem_eq_powerset (k : K) (f : Finset K → ℝ) :
    (∑ Y ∈ Finset.univ.filter (fun Y : Finset K => k ∈ Y), f Y) =
      ∑ Y ∈ (Finset.univ.erase k).powerset, f (insert k Y) := by
  symm
  refine Finset.sum_nbij (fun Y => insert k Y) ?_ ?_ ?_ ?_
  · intro Y _
    simp
  · intro Y₁ hY₁ Y₂ hY₂ hEq
    have hk₁ : k ∉ Y₁ := (mem_powerset_erase_univ_iff k Y₁).mp hY₁
    have hk₂ : k ∉ Y₂ := (mem_powerset_erase_univ_iff k Y₂).mp hY₂
    have herase : (insert k Y₁).erase k = (insert k Y₂).erase k := congrArg (·.erase k) hEq
    rwa [Finset.erase_insert hk₁, Finset.erase_insert hk₂] at herase
  · intro Z hZ
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hZ
    refine ⟨Z.erase k, ?_, Finset.insert_erase hZ⟩
    rw [Finset.mem_coe, mem_powerset_erase_univ_iff]
    exact Finset.notMem_erase k Z
  · intro _ _
    rfl

lemma sum_univ_split_task (k : K) (f : Finset K → ℝ) :
    (∑ Y : Finset K, f Y) =
      ∑ Y ∈ (Finset.univ.erase k).powerset, (f (insert k Y) + f Y) := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun Y : Finset K => k ∈ Y) f]
  rw [sum_filter_mem_eq_powerset k f]
  have hfilter :
      Finset.univ.filter (fun Y : Finset K => k ∉ Y) = (Finset.univ.erase k).powerset := by
    ext Y
    rw [Finset.mem_filter, mem_powerset_erase_univ_iff]
    simp
  rw [hfilter, ← Finset.sum_add_distrib]

end Combinatorics

/-! ### Part 2: Exact Formula for `I.optMinPay (separable K)` -/

section SeparableOpt

variable {K : Type*} [Fintype K] [DecidableEq K]

lemma p_pos (I : Instance K) (k : K) : 0 < I.p k :=
  lt_of_le_of_lt (I.q_nonneg k) (I.q_lt_p k)

lemma p_nonneg (I : Instance K) (k : K) : 0 ≤ I.p k :=
  le_of_lt (p_pos I k)

lemma p_sub_q_pos (I : Instance K) (k : K) : 0 < I.p k - I.q k :=
  sub_pos.mpr (I.q_lt_p k)

/-- Closed-form value of `OPT^Sep_MinPay(I)`: `∑_{k ∈ K} p_k c_k / (p_k - q_k)`. -/
noncomputable def sepVal (I : Instance K) : ℝ :=
  ∑ k : K, I.p k * (I.c k / (I.p k - I.q k))

lemma sepVal_nonneg (I : Instance K) : 0 ≤ sepVal I := by
  unfold sepVal
  refine Finset.sum_nonneg ?_
  intro k _
  exact mul_nonneg (p_nonneg I k) (div_nonneg (le_of_lt (I.c_pos k)) (le_of_lt (p_sub_q_pos I k)))

lemma sepVal_pos [Nonempty K] (I : Instance K) : 0 < sepVal I := by
  unfold sepVal
  refine Finset.sum_pos ?_ Finset.univ_nonempty
  intro k _
  exact mul_pos (p_pos I k) (div_pos (I.c_pos k) (p_sub_q_pos I k))

lemma expect_separable_eq (I : Instance K) (t₀ : ℝ) (tk : K → ℝ) (t : Finset K → ℝ)
    (ht : ∀ Y, t Y = t₀ + ∑ k ∈ Y, tk k) (S : Finset K) :
    I.expect S t = t₀ + ∑ k : K, (if k ∈ S then I.p k else I.q k) * tk k := by
  change (∑ Y : Finset K, I.P S Y * t Y) = _
  have h1 :
      (∑ Y : Finset K, I.P S Y * t Y) =
        (∑ Y : Finset K, I.P S Y * t₀) +
          ∑ Y : Finset K, ∑ k : K, (if k ∈ Y then I.P S Y * tk k else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro Y _
    rw [ht Y, mul_add, Finset.mul_sum, ← Finset.sum_filter]
    congr 2
    ext k
    simp
  rw [h1, ← Finset.sum_mul, I.P_sum S, one_mul, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [← Finset.sum_filter, ← Finset.sum_mul]
  by_cases hk : k ∈ S
  · rw [if_pos hk, I.marginal_mem S k hk]
  · rw [if_neg hk, I.marginal_not_mem S k hk]

lemma optMinPay_separable_le (I : Instance K) :
    I.optMinPay (separable K) ≤ ENNReal.ofReal (sepVal I) := by
  let tk : K → ℝ := fun k => I.c k / (I.p k - I.q k)
  let t : Finset K → ℝ := fun Y => 0 + ∑ k ∈ Y, tk k
  let B : ℝ := ∑ k : K, tk k
  have htk_nonneg : ∀ k, 0 ≤ tk k := fun k =>
    div_nonneg (le_of_lt (I.c_pos k)) (le_of_lt (p_sub_q_pos I k))
  have hB_nonneg : 0 ≤ B := Finset.sum_nonneg (fun k _ => htk_nonneg k)
  have ht_sep : t ∈ separable K := ⟨0, tk, le_rfl, htk_nonneg, fun _ => rfl⟩
  have ht_B : ∀ Y, t Y ≤ B := by
    intro Y
    dsimp [t, B]
    rw [zero_add]
    exact Finset.sum_le_univ_sum_of_nonneg htk_nonneg
  have hutil_const : ∀ S : Finset K,
      I.expect S t - I.cost S = ∑ k : K, I.q k * tk k := by
    intro S
    rw [expect_separable_eq I 0 tk t (fun _ => rfl) S, zero_add]
    unfold Instance.cost
    have hcost : (∑ k ∈ S, I.c k) = ∑ k : K, (if k ∈ S then I.c k else 0) := by
      have hS : S = Finset.univ.filter (fun k : K => k ∈ S) := by ext k; simp
      conv_lhs => rw [hS]
      rw [Finset.sum_filter]
    rw [hcost, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro k _
    have hne : I.p k - I.q k ≠ 0 := ne_of_gt (p_sub_q_pos I k)
    by_cases hk : k ∈ S
    · simp only [hk, ↓reduceIte, tk]
      field_simp [hne]
      ring
    · simp [hk, tk]
  have ht_IC : I.Implements t Finset.univ := by
    intro S
    change I.expect S t - I.cost S ≤ I.expect Finset.univ t - I.cost Finset.univ
    rw [hutil_const S, hutil_const Finset.univ]
  have hexp_univ : I.expect Finset.univ t = sepVal I := by
    rw [expect_separable_eq I 0 tk t (fun _ => rfl) Finset.univ, zero_add]
    simp [sepVal, tk]
  unfold Instance.optMinPay ContractSetting.optMinPay
  refine iInf₂_le_of_le B hB_nonneg ?_
  unfold ContractSetting.optFixedBudget
  refine iInf₂_le_of_le t ⟨ht_sep, ht_IC, ht_B⟩ ?_
  change ENNReal.ofReal (I.expect Finset.univ t) ≤ ENNReal.ofReal (sepVal I)
  rw [hexp_univ]

lemma le_optMinPay_separable (I : Instance K) :
    ENNReal.ofReal (sepVal I) ≤ I.optMinPay (separable K) := by
  unfold Instance.optMinPay ContractSetting.optMinPay ContractSetting.optFixedBudget
  refine le_iInf₂ ?_
  intro B _
  refine le_iInf₂ ?_
  rintro t ⟨⟨t₀, tk, ht₀, _, ht_eq⟩, ht_IC, _⟩
  apply ENNReal.ofReal_le_ofReal
  change sepVal I ≤ I.expect Finset.univ t
  rw [expect_separable_eq I t₀ tk t ht_eq Finset.univ]
  simp only [Finset.mem_univ, ↓reduceIte]
  have hterm : ∀ k : K, I.p k * (I.c k / (I.p k - I.q k)) ≤ I.p k * tk k := by
    intro k
    have hIC_k :
        I.expect (Finset.univ.erase k) t - I.cost (Finset.univ.erase k) ≤
          I.expect Finset.univ t - I.cost Finset.univ :=
      ht_IC (Finset.univ.erase k)
    rw [expect_separable_eq I t₀ tk t ht_eq (Finset.univ.erase k),
      expect_separable_eq I t₀ tk t ht_eq Finset.univ] at hIC_k
    have hexp_diff :
        (∑ j : K, (if j ∈ (Finset.univ : Finset K) then I.p j else I.q j) * tk j) -
          (∑ j : K, (if j ∈ Finset.univ.erase k then I.p j else I.q j) * tk j) =
          (I.p k - I.q k) * tk k := by
      rw [← Finset.sum_sub_distrib, ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
      have hrest :
          ∑ j ∈ Finset.univ.erase k,
            ((if j ∈ (Finset.univ : Finset K) then I.p j else I.q j) * tk j -
              (if j ∈ Finset.univ.erase k then I.p j else I.q j) * tk j) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro j hj
        simp [hj]
      rw [hrest, add_zero]
      simp [sub_mul]
    have hcost_diff : I.cost Finset.univ - I.cost (Finset.univ.erase k) = I.c k := by
      unfold Instance.cost
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
      ring
    have hck_le : I.c k ≤ (I.p k - I.q k) * tk k := by linarith
    have hdiv_le : I.c k / (I.p k - I.q k) ≤ tk k :=
      (div_le_iff₀ (p_sub_q_pos I k)).mpr (by linarith)
    exact mul_le_mul_of_nonneg_left hdiv_le (p_nonneg I k)
  have hsum_le : sepVal I ≤ ∑ k : K, I.p k * tk k :=
    Finset.sum_le_sum (fun k _ => hterm k)
  linarith

lemma optMinPay_separable_eq (I : Instance K) :
    I.optMinPay (separable K) = ENNReal.ofReal (sepVal I) :=
  le_antisymm (optMinPay_separable_le I) (le_optMinPay_separable I)

end SeparableOpt

/-! ### Part 3: Upper Bound `priceOfSeparation ≤ |K|` under Independence -/

section UpperBound

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- Weight of outcomes `Y` on tasks other than `k` when exerting effort on `K \ {k}`. -/
def wRest (I : Instance K) (k : K) (Y : Finset K) : ℝ :=
  ∏ j ∈ Finset.univ.erase k, (if j ∈ Y then I.p j else 1 - I.p j)

lemma wRest_nonneg (I : Instance K) (k : K) (Y : Finset K) :
    0 ≤ wRest I k Y := by
  unfold wRest
  refine Finset.prod_nonneg ?_
  intro j _
  split_ifs
  · exact p_nonneg I j
  · linarith [I.p_le_one j]

lemma indep_P_univ_insert (I : Instance K) (hInd : I.IsIndependent) (k : K) (Y : Finset K) :
    I.P Finset.univ (insert k Y) = I.p k * wRest I k Y := by
  rw [hInd Finset.univ (insert k Y), ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
  simp only [Finset.mem_univ, ↓reduceIte, Finset.mem_insert_self]
  congr 1
  unfold wRest
  refine Finset.prod_congr rfl ?_
  intro j hj
  have hjne : j ≠ k := Finset.ne_of_mem_erase hj
  simp [hjne]

lemma indep_P_univ_not_mem (I : Instance K) (hInd : I.IsIndependent) (k : K) (Y : Finset K)
    (hkY : k ∉ Y) :
    I.P Finset.univ Y = (1 - I.p k) * wRest I k Y := by
  rw [hInd Finset.univ Y, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
  simp only [Finset.mem_univ, ↓reduceIte, hkY]
  rfl

lemma indep_P_erase_insert (I : Instance K) (hInd : I.IsIndependent) (k : K) (Y : Finset K) :
    I.P (Finset.univ.erase k) (insert k Y) = I.q k * wRest I k Y := by
  rw [hInd (Finset.univ.erase k) (insert k Y),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
  simp only [Finset.notMem_erase, ↓reduceIte, Finset.mem_insert_self]
  congr 1
  unfold wRest
  refine Finset.prod_congr rfl ?_
  intro j hj
  have hjne : j ≠ k := Finset.ne_of_mem_erase hj
  simp [hj, hjne]

lemma indep_P_erase_not_mem (I : Instance K) (hInd : I.IsIndependent) (k : K) (Y : Finset K)
    (hkY : k ∉ Y) :
    I.P (Finset.univ.erase k) Y = (1 - I.q k) * wRest I k Y := by
  rw [hInd (Finset.univ.erase k) Y,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
  simp only [Finset.notMem_erase, ↓reduceIte, hkY]
  congr 1
  unfold wRest
  refine Finset.prod_congr rfl ?_
  intro j hj
  simp [hj]

lemma bundle_task_lower_bound (I : Instance K) (hInd : I.IsIndependent)
    (t : Finset K → ℝ) (ht_bun : t ∈ bundle K) (ht_IC : I.Implements t Finset.univ) (k : K) :
    I.p k * (I.c k / (I.p k - I.q k)) ≤ I.expect Finset.univ t := by
  have hexp_univ :
      I.expect Finset.univ t =
        ∑ Y ∈ (Finset.univ.erase k).powerset,
          (I.p k * wRest I k Y * t (insert k Y) + (1 - I.p k) * wRest I k Y * t Y) := by
    change (∑ Y : Finset K, I.P Finset.univ Y * t Y) = _
    rw [sum_univ_split_task k]
    refine Finset.sum_congr rfl ?_
    intro Y hY
    have hkY : k ∉ Y := (mem_powerset_erase_univ_iff k Y).mp hY
    rw [indep_P_univ_insert I hInd k Y, indep_P_univ_not_mem I hInd k Y hkY]
  have hexp_erase :
      I.expect (Finset.univ.erase k) t =
        ∑ Y ∈ (Finset.univ.erase k).powerset,
          (I.q k * wRest I k Y * t (insert k Y) + (1 - I.q k) * wRest I k Y * t Y) := by
    change (∑ Y : Finset K, I.P (Finset.univ.erase k) Y * t Y) = _
    rw [sum_univ_split_task k]
    refine Finset.sum_congr rfl ?_
    intro Y hY
    have hkY : k ∉ Y := (mem_powerset_erase_univ_iff k Y).mp hY
    rw [indep_P_erase_insert I hInd k Y, indep_P_erase_not_mem I hInd k Y hkY]
  have hexp_diff :
      I.expect Finset.univ t - I.expect (Finset.univ.erase k) t =
        (I.p k - I.q k) *
          ∑ Y ∈ (Finset.univ.erase k).powerset, wRest I k Y * (t (insert k Y) - t Y) := by
    rw [hexp_univ, hexp_erase, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro Y _
    ring
  have hcost_diff : I.cost Finset.univ - I.cost (Finset.univ.erase k) = I.c k := by
    unfold Instance.cost
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
    ring
  have hIC_k :
      I.expect (Finset.univ.erase k) t - I.cost (Finset.univ.erase k) ≤
        I.expect Finset.univ t - I.cost Finset.univ :=
    ht_IC (Finset.univ.erase k)
  let M : ℝ := ∑ Y ∈ (Finset.univ.erase k).powerset, wRest I k Y * (t (insert k Y) - t Y)
  have hck_le : I.c k ≤ (I.p k - I.q k) * M := by linarith
  have hM_ge : I.c k / (I.p k - I.q k) ≤ M :=
    (div_le_iff₀ (p_sub_q_pos I k)).mpr (by linarith)
  have hpM_le : I.p k * M ≤ I.expect Finset.univ t := by
    rw [hexp_univ]
    dsimp [M]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro Y _
    have hw : 0 ≤ wRest I k Y := wRest_nonneg I k Y
    have htY : 0 ≤ t Y := ht_bun Y
    have hprod_nonneg : 0 ≤ wRest I k Y * t Y := mul_nonneg hw htY
    nlinarith
  exact le_trans (mul_le_mul_of_nonneg_left hM_ge (p_nonneg I k)) hpM_le

lemma le_optMinPay_bundle [Nonempty K] (I : Instance K) (hInd : I.IsIndependent) :
    ENNReal.ofReal (sepVal I / (Fintype.card K : ℝ)) ≤ I.optMinPay (bundle K) := by
  unfold Instance.optMinPay ContractSetting.optMinPay ContractSetting.optFixedBudget
  refine le_iInf₂ ?_
  intro B _
  refine le_iInf₂ ?_
  rintro t ⟨ht_bun, ht_IC, _⟩
  apply ENNReal.ofReal_le_ofReal
  change sepVal I / (Fintype.card K : ℝ) ≤ I.expect Finset.univ t
  have hsum :
      sepVal I ≤ ∑ _k : K, I.expect Finset.univ t :=
    Finset.sum_le_sum (fun k _ => bundle_task_lower_bound I hInd t ht_bun ht_IC k)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hn_pos : (0 : ℝ) < (Fintype.card K : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  exact (div_le_iff₀ hn_pos).mpr (by linarith)

lemma priceOfSeparation_le_card [Nonempty K] :
    priceOfSeparation (fun I T => I.optMinPay T) {I : Instance K | I.IsIndependent} ≤
      (Fintype.card K : ℝ≥0∞) := by
  unfold priceOfSeparation
  refine iSup₂_le ?_
  intro I hInd
  have ha : I.optMinPay (separable K) = ENNReal.ofReal (sepVal I) :=
    optMinPay_separable_eq I
  have ha_ne_top : I.optMinPay (separable K) ≠ ⊤ := by
    rw [ha]
    exact ENNReal.ofReal_ne_top
  dsimp only
  unfold sepRatio
  rw [if_neg (fun h => ha_ne_top h.1), ha]
  apply ENNReal.div_le_of_le_mul
  have hn_pos : (0 : ℝ) < (Fintype.card K : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hdiv_nonneg : 0 ≤ sepVal I / (Fintype.card K : ℝ) :=
    div_nonneg (sepVal_nonneg I) (le_of_lt hn_pos)
  have hsplit :
      ENNReal.ofReal (sepVal I) =
        ENNReal.ofReal (sepVal I / (Fintype.card K : ℝ)) * (Fintype.card K : ℝ≥0∞) := by
    have heq : sepVal I = sepVal I / (Fintype.card K : ℝ) * (Fintype.card K : ℝ) :=
      (div_mul_cancel₀ (sepVal I) (ne_of_gt hn_pos)).symm
    conv_lhs => rw [heq]
    rw [ENNReal.ofReal_mul hdiv_nonneg, ENNReal.ofReal_natCast]
  rw [hsplit, mul_comm]
  exact mul_le_mul_of_nonneg_left (le_optMinPay_bundle I hInd) zero_le

end UpperBound

/-! ### Part 4: Lower Bound `|K| ≤ priceOfSeparation` via Near-Deterministic Instances -/

section LowerBound

variable {K : Type*} [Fintype K] [DecidableEq K]

lemma mul_eps_pow_le (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (m : ℕ) :
    (m : ℝ) * ε * (1 - ε) ^ m ≤ 1 - (1 - ε) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : 0 ≤ 1 - ε := by linarith
    have hpow_le : (1 - ε) ^ (m + 1) ≤ 1 := pow_le_one₀ h1 (by linarith)
    have hε_mul_le : ε * (1 - ε) ^ (m + 1) ≤ ε := mul_le_of_le_one_right hε0 hpow_le
    have hstep :
        (m : ℝ) * ε * (1 - ε) ^ m * (1 - ε) ≤ (1 - (1 - ε) ^ m) * (1 - ε) :=
      mul_le_mul_of_nonneg_right ih h1
    push_cast
    rw [pow_succ] at hpow_le hε_mul_le ⊢
    linarith

lemma bernoulli_one_sub (ε : ℝ) (_hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (n : ℕ) :
    1 - (n : ℝ) * ε ≤ (1 - ε) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 0 ≤ 1 - ε := by linarith
    have hstep : (1 - (n : ℝ) * ε) * (1 - ε) ≤ (1 - ε) ^ n * (1 - ε) :=
      mul_le_mul_of_nonneg_right ih h1
    have hsq : 0 ≤ (n : ℝ) * (ε * ε) :=
      mul_nonneg (Nat.cast_nonneg n) (mul_self_nonneg ε)
    push_cast
    rw [pow_succ]
    nlinarith

/-- Symmetric independent instance `I_ε` with `p_k = 1`, `q_k = 1 - ε`, `c_k = ε` (`0 < ε < 1`). -/
def hardInstance (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) : Instance K where
  p := fun _ => 1
  q := fun _ => 1 - ε
  c := fun _ => ε
  P := fun S Y =>
    ∏ k : K, if k ∈ S then (if k ∈ Y then (1 : ℝ) else 1 - 1)
      else (if k ∈ Y then 1 - ε else 1 - (1 - ε))
  q_nonneg := fun _ => by linarith
  q_lt_p := fun _ => by linarith
  p_le_one := fun _ => le_rfl
  c_pos := fun _ => hε0
  P_nonneg := by
    intro S Y
    refine Finset.prod_nonneg ?_
    intro k _
    split_ifs <;> linarith
  P_sum := by
    intro S
    let r : K → ℝ := fun k => if k ∈ S then 1 else 1 - ε
    have hcongr :
        (∑ Y : Finset K,
          ∏ k : K, if k ∈ S then (if k ∈ Y then (1 : ℝ) else 1 - 1)
            else (if k ∈ Y then 1 - ε else 1 - (1 - ε))) =
          ∑ Y ∈ (Finset.univ : Finset K).powerset,
            ∏ k ∈ Finset.univ, (if k ∈ Y then r k else 1 - r k) := by
      have hpow : (Finset.univ : Finset K).powerset = Finset.univ := by
        ext Y
        simp
      rw [hpow]
      refine Finset.sum_congr rfl ?_
      intro Y _
      refine Finset.prod_congr rfl ?_
      intro k _
      by_cases hkS : k ∈ S <;> simp [r, hkS]
    rw [hcongr]
    exact sum_powerset_prod_ite Finset.univ r
  marginal_mem := by
    intro S k hkS
    rw [sum_filter_mem_eq_powerset k]
    let r : K → ℝ := fun j => if j ∈ S then 1 else 1 - ε
    have hcongr :
        (∑ Y ∈ (Finset.univ.erase k).powerset,
          ∏ j : K, if j ∈ S then (if j ∈ insert k Y then (1 : ℝ) else 1 - 1)
            else (if j ∈ insert k Y then 1 - ε else 1 - (1 - ε))) =
          ∑ Y ∈ (Finset.univ.erase k).powerset,
            1 * ∏ j ∈ Finset.univ.erase k, (if j ∈ Y then r j else 1 - r j) := by
      refine Finset.sum_congr rfl ?_
      intro Y _
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
      simp only [hkS, ↓reduceIte, Finset.mem_insert_self]
      congr 1
      refine Finset.prod_congr rfl ?_
      intro j hj
      have hjne : j ≠ k := Finset.ne_of_mem_erase hj
      by_cases hjS : j ∈ S <;> simp [r, hjS, hjne]
    rw [hcongr]
    simp only [one_mul]
    exact sum_powerset_prod_ite (Finset.univ.erase k) r
  marginal_not_mem := by
    intro S k hkS
    rw [sum_filter_mem_eq_powerset k]
    let r : K → ℝ := fun j => if j ∈ S then 1 else 1 - ε
    have hcongr :
        (∑ Y ∈ (Finset.univ.erase k).powerset,
          ∏ j : K, if j ∈ S then (if j ∈ insert k Y then (1 : ℝ) else 1 - 1)
            else (if j ∈ insert k Y then 1 - ε else 1 - (1 - ε))) =
          ∑ Y ∈ (Finset.univ.erase k).powerset,
            (1 - ε) * ∏ j ∈ Finset.univ.erase k, (if j ∈ Y then r j else 1 - r j) := by
      refine Finset.sum_congr rfl ?_
      intro Y _
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
      simp only [hkS, ↓reduceIte, Finset.mem_insert_self]
      congr 1
      refine Finset.prod_congr rfl ?_
      intro j hj
      have hjne : j ≠ k := Finset.ne_of_mem_erase hj
      by_cases hjS : j ∈ S <;> simp [r, hjS, hjne]
    rw [hcongr, ← Finset.mul_sum, sum_powerset_prod_ite (Finset.univ.erase k) r, mul_one]
  P_univ_univ_pos := by
    simp

lemma hardInstance_isIndependent (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    (hardInstance ε hε0 hε1 : Instance K).IsIndependent :=
  fun _ _ => rfl

lemma hardInstance_sepVal (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    sepVal (hardInstance ε hε0 hε1 : Instance K) = (Fintype.card K : ℝ) := by
  unfold sepVal hardInstance
  simp [div_self (ne_of_gt hε0)]

lemma hardInstance_P_univ (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (S : Finset K) :
    (hardInstance ε hε0 hε1 : Instance K).P S Finset.univ =
      (1 - ε) ^ (Finset.univ \ S).card := by
  dsimp [hardInstance]
  simp only [Finset.mem_univ, ↓reduceIte]
  rw [prod_ite_mem_eq Finset.univ S (Finset.subset_univ S)]
  simp

lemma hardInstance_optMinPay_bundle_le (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    (hardInstance ε hε0 hε1 : Instance K).optMinPay (bundle K) ≤
      ENNReal.ofReal (((1 - ε) ^ Fintype.card K)⁻¹) := by
  let I : Instance K := hardInstance ε hε0 hε1
  let n : ℕ := Fintype.card K
  let B : ℝ := ((1 - ε) ^ n)⁻¹
  let t : Finset K → ℝ := fun Y => if Y = Finset.univ then B else 0
  have h1eps_pos : 0 < 1 - ε := by linarith
  have hpow_pos : 0 < (1 - ε) ^ n := pow_pos h1eps_pos n
  have hB_pos : 0 < B := inv_pos.mpr hpow_pos
  have hB_nonneg : 0 ≤ B := le_of_lt hB_pos
  have ht_bun : t ∈ bundle K := by
    intro Y
    dsimp [t]
    split_ifs <;> linarith
  have ht_B : ∀ Y, t Y ≤ B := by
    intro Y
    dsimp [t]
    split_ifs <;> linarith
  have hexp : ∀ S : Finset K, I.expect S t = (1 - ε) ^ (Finset.univ \ S).card * B := by
    intro S
    change (∑ Y : Finset K, I.P S Y * t Y) = _
    rw [Finset.sum_eq_single Finset.univ]
    · simp [t, I, hardInstance_P_univ ε hε0 hε1 S]
    · intro Y _ hYne
      simp [t, hYne]
    · intro hnot
      exact absurd (Finset.mem_univ Finset.univ) hnot
  have ht_IC : I.Implements t Finset.univ := by
    intro S
    change I.expect S t - I.cost S ≤ I.expect Finset.univ t - I.cost Finset.univ
    rw [hexp S, hexp Finset.univ]
    simp only [sdiff_self, Finset.bot_eq_empty, Finset.card_empty, pow_zero, one_mul]
    have hcost_diff : I.cost Finset.univ - I.cost S = ((Finset.univ \ S).card : ℝ) * ε := by
      unfold Instance.cost
      have hunion : (Finset.univ : Finset K) = S ∪ (Finset.univ \ S) := by
        ext k
        simp
      have hdisj : Disjoint S (Finset.univ \ S) := disjoint_sdiff_self_right
      conv_lhs => rw [hunion, Finset.sum_union hdisj]
      simp [I, hardInstance]
    let m : ℕ := (Finset.univ \ S).card
    have hm_le : m ≤ n := by
      dsimp [m, n]
      rw [← Finset.card_univ]
      exact Finset.card_le_card (Finset.subset_univ _)
    have hpow_mono : (1 - ε) ^ n ≤ (1 - ε) ^ m :=
      pow_le_pow_of_le_one (le_of_lt h1eps_pos) (by linarith) hm_le
    have hm_nonneg : 0 ≤ (m : ℝ) * ε := mul_nonneg (Nat.cast_nonneg m) (le_of_lt hε0)
    have hineq1 : (m : ℝ) * ε * (1 - ε) ^ n ≤ (m : ℝ) * ε * (1 - ε) ^ m :=
      mul_le_mul_of_nonneg_left hpow_mono hm_nonneg
    have hineq2 : (m : ℝ) * ε * (1 - ε) ^ m ≤ 1 - (1 - ε) ^ m :=
      mul_eps_pow_le ε (le_of_lt hε0) (le_of_lt hε1) m
    have hineq3 : (m : ℝ) * ε * (1 - ε) ^ n ≤ 1 - (1 - ε) ^ m := le_trans hineq1 hineq2
    have hmulB : ((m : ℝ) * ε * (1 - ε) ^ n) * B ≤ (1 - (1 - ε) ^ m) * B :=
      mul_le_mul_of_nonneg_right hineq3 hB_nonneg
    have hcancel : ((m : ℝ) * ε * (1 - ε) ^ n) * B = (m : ℝ) * ε := by
      dsimp [B]
      rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hpow_pos), mul_one]
    rw [hcancel] at hmulB
    dsimp [m] at hmulB
    linarith
  unfold Instance.optMinPay ContractSetting.optMinPay
  refine iInf₂_le_of_le B hB_nonneg ?_
  unfold ContractSetting.optFixedBudget
  refine iInf₂_le_of_le t ⟨ht_bun, ht_IC, ht_B⟩ ?_
  change ENNReal.ofReal (I.expect Finset.univ t) ≤ ENNReal.ofReal B
  rw [hexp Finset.univ]
  simp

lemma ofReal_card_mul_pow_le_priceOfSeparation [Nonempty K]
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ENNReal.ofReal ((Fintype.card K : ℝ) * (1 - ε) ^ Fintype.card K) ≤
      priceOfSeparation (fun I T => I.optMinPay T) {I : Instance K | I.IsIndependent} := by
  let I : Instance K := hardInstance ε hε0 hε1
  let n : ℕ := Fintype.card K
  have hInd : I ∈ {I : Instance K | I.IsIndependent} :=
    hardInstance_isIndependent ε hε0 hε1
  have hsep : I.optMinPay (separable K) = (n : ℝ≥0∞) := by
    rw [optMinPay_separable_eq I, hardInstance_sepVal ε hε0 hε1, ENNReal.ofReal_natCast]
  have hsep_ne_top : I.optMinPay (separable K) ≠ ⊤ := by
    rw [hsep]
    exact ENNReal.natCast_ne_top n
  have hbun_le : I.optMinPay (bundle K) ≤ ENNReal.ofReal (((1 - ε) ^ n)⁻¹) :=
    hardInstance_optMinPay_bundle_le ε hε0 hε1
  have hpow_pos : 0 < (1 - ε) ^ n := pow_pos (by linarith) n
  have hinv_pos : 0 < ((1 - ε) ^ n)⁻¹ := inv_pos.mpr hpow_pos
  have hinv_ne_zero : ENNReal.ofReal (((1 - ε) ^ n)⁻¹) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hinv_pos).ne'
  have hinv_ne_top : ENNReal.ofReal (((1 - ε) ^ n)⁻¹) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hprod_eq :
      ENNReal.ofReal ((n : ℝ) * (1 - ε) ^ n) * ENNReal.ofReal (((1 - ε) ^ n)⁻¹) = (n : ℝ≥0∞) := by
    have hnonneg : 0 ≤ (n : ℝ) * (1 - ε) ^ n :=
      mul_nonneg (Nat.cast_nonneg n) (le_of_lt hpow_pos)
    rw [← ENNReal.ofReal_mul hnonneg, mul_assoc, mul_inv_cancel₀ (ne_of_gt hpow_pos),
      mul_one, ENNReal.ofReal_natCast]
  have hle_div :
      ENNReal.ofReal ((n : ℝ) * (1 - ε) ^ n) ≤
        (n : ℝ≥0∞) / ENNReal.ofReal (((1 - ε) ^ n)⁻¹) := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hinv_ne_zero) (Or.inl hinv_ne_top)]
    exact le_of_eq hprod_eq
  have hdiv_mono :
      (n : ℝ≥0∞) / ENNReal.ofReal (((1 - ε) ^ n)⁻¹) ≤ (n : ℝ≥0∞) / I.optMinPay (bundle K) :=
    ENNReal.div_le_div_left hbun_le (n : ℝ≥0∞)
  have hratio_eq :
      sepRatio (I.optMinPay (separable K)) (I.optMinPay (bundle K)) =
        (n : ℝ≥0∞) / I.optMinPay (bundle K) := by
    unfold sepRatio
    rw [if_neg (fun h => hsep_ne_top h.1), hsep]
  have hle_ratio :
      ENNReal.ofReal ((n : ℝ) * (1 - ε) ^ n) ≤
        sepRatio (I.optMinPay (separable K)) (I.optMinPay (bundle K)) := by
    rw [hratio_eq]
    exact le_trans hle_div hdiv_mono
  unfold priceOfSeparation
  exact le_trans hle_ratio (le_iSup₂ (f := fun J _ =>
    sepRatio (J.optMinPay (separable K)) (J.optMinPay (bundle K))) I hInd)

lemma card_le_priceOfSeparation [Nonempty K] :
    (Fintype.card K : ℝ≥0∞) ≤
      priceOfSeparation (fun I T => I.optMinPay T) {I : Instance K | I.IsIndependent} := by
  let P : ℝ≥0∞ := priceOfSeparation (fun I T => I.optMinPay T) {I : Instance K | I.IsIndependent}
  let n : ℕ := Fintype.card K
  change (n : ℝ≥0∞) ≤ P
  refine le_of_not_gt ?_
  intro hlt
  have hP_ne_top : P ≠ ⊤ := ne_top_of_lt hlt
  let r : ℝ := P.toReal
  have hr_nonneg : 0 ≤ r := ENNReal.toReal_nonneg
  have hP_eq : ENNReal.ofReal r = P := ENNReal.ofReal_toReal hP_ne_top
  have hr_lt_n : r < (n : ℝ) := by
    refine lt_of_not_ge ?_
    intro hge
    have hle : (n : ℝ≥0∞) ≤ P := by
      rw [← ENNReal.ofReal_natCast, ← hP_eq]
      exact ENNReal.ofReal_le_ofReal hge
    exact not_lt_of_ge hle hlt
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  let δ : ℝ := (n : ℝ) - r
  have hδ_pos : 0 < δ := sub_pos.mpr hr_lt_n
  have hdenom_pos : 0 < 2 * (n : ℝ) ^ 2 := by positivity
  let ε : ℝ := min (1 / 2 : ℝ) (δ / (2 * (n : ℝ) ^ 2))
  have hε0 : 0 < ε := lt_min (by norm_num) (div_pos hδ_pos hdenom_pos)
  have hε1 : ε < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hε_le : ε ≤ δ / (2 * (n : ℝ) ^ 2) := min_le_right _ _
  have hnsq_eps : (n : ℝ) ^ 2 * ε ≤ δ / 2 := by
    have hmul : ε * (2 * (n : ℝ) ^ 2) ≤ δ := ( le_div_iff₀ hdenom_pos ).mp hε_le
    linarith
  have hbern : 1 - (n : ℝ) * ε ≤ (1 - ε) ^ n :=
    bernoulli_one_sub ε (le_of_lt hε0) (le_of_lt hε1) n
  have hval_ge : r + δ / 2 ≤ (n : ℝ) * (1 - ε) ^ n := by
    have h1 : (n : ℝ) * (1 - (n : ℝ) * ε) ≤ (n : ℝ) * (1 - ε) ^ n :=
      mul_le_mul_of_nonneg_left hbern (le_of_lt hn_pos)
    dsimp [δ] at hnsq_eps ⊢
    nlinarith
  have hval_nonneg : 0 ≤ (n : ℝ) * (1 - ε) ^ n := by linarith
  have hofReal_le : ENNReal.ofReal ((n : ℝ) * (1 - ε) ^ n) ≤ ENNReal.ofReal r := by
    rw [hP_eq]
    exact ofReal_card_mul_pow_le_priceOfSeparation ε hε0 hε1
  have hreal_le : (n : ℝ) * (1 - ε) ^ n ≤ r := by
    have hto := ENNReal.toReal_mono ENNReal.ofReal_ne_top hofReal_le
    rwa [ENNReal.toReal_ofReal hval_nonneg, ENNReal.toReal_ofReal hr_nonneg] at hto
  linarith

end LowerBound

theorem theorem_2_proof (K : Type*) [Fintype K] [DecidableEq K] [Nonempty K] :
    priceOfSeparation (fun I T => I.optMinPay T) {I : Instance K | I.IsIndependent} =
      (Fintype.card K : ℝ≥0∞) :=
  le_antisymm priceOfSeparation_le_card card_le_priceOfSeparation

end MultitaskContracts_Theorem2_Proof

open MultitaskContracts
open scoped ENNReal

theorem solution (K : Type*) [Fintype K] [DecidableEq K] [Nonempty K] :
    priceOfSeparation (fun I T => I.optMinPay T) {I : Instance K | I.IsIndependent} =
      (Fintype.card K : ℝ≥0∞) :=
  MultitaskContracts_Theorem2_Proof.theorem_2_proof K
