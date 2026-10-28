-- Prove2me | solution 1 for OAI.MarkovSuperreflexivity.hasEquivalentUCNorm_of_finiteTriangularObstruction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T10:41:23.765992+00:00
-- url     : https://prove2.me/submissions/16c24604-8409-4723-b8db-f700cc084e7c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MarkovType
import Definitions.Def_OAISMk002
import Theorems.Thm_OAI_MarkovSuperreflexivity_FiniteTriangularObstruction_sequenceL2

section
-- module Solutions.OAIS_Markov.MarkovType_CoefficientBasic
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ}

theorem CoefficientBasic.smul {K : ℝ} {x : Fin n → E}
    (hx : CoefficientBasic K x) (c : Fin n → ℝ) :
    CoefficientBasic K (fun i => c i • x i) := by
  intro a k hk
  simpa only [smul_smul] using hx (fun i => a i * c i) k hk

theorem CoefficientBasic.mono {K L : ℝ} {x : Fin n → E}
    (hx : CoefficientBasic K x) (hKL : K ≤ L) : CoefficientBasic L x := by
  intro a k hk
  exact (hx a k hk).trans (mul_le_mul_of_nonneg_right hKL (norm_nonneg _))

theorem CoefficientBasic.norm_prefix_le {K : ℝ} {x : Fin n → E}
    (hx : CoefficientBasic K x) (k : ℕ) (hk : k ≤ n) :
    ‖∑ i : Fin n, if i.val < k then x i else 0‖ ≤ K * ‖∑ i : Fin n, x i‖ := by
  simpa only [one_smul] using hx (fun _ => 1) k hk

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_CoefficientFunctional
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ} {K : ℝ} {x : Fin n → E}

theorem CoefficientBasic.norm_term_le (hx : CoefficientBasic K x)
    (a : Fin n → ℝ) (j : Fin n) :
    ‖a j • x j‖ ≤ (2 * K) * ‖∑ i, a i • x i‖ := by
  have hdifference :
      (∑ i : Fin n, if i.val < j.val + 1 then a i • x i else 0) -
        (∑ i : Fin n, if i.val < j.val then a i • x i else 0) = a j • x j := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ = ∑ i : Fin n, if i = j then a j • x j else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hij : i = j
        · subst i
          simp
        · have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
          have hiff : i.val < j.val + 1 ↔ i.val < j.val := by omega
          simp only [hiff, ite_eq_right hij, sub_self]
      _ = _ := by simp
  calc
    ‖a j • x j‖ = ‖(∑ i : Fin n, if i.val < j.val + 1 then a i • x i else 0) -
        (∑ i : Fin n, if i.val < j.val then a i • x i else 0)‖ :=
      congrArg norm hdifference.symm
    _ ≤ ‖∑ i : Fin n, if i.val < j.val + 1 then a i • x i else 0‖ +
        ‖∑ i : Fin n, if i.val < j.val then a i • x i else 0‖ := norm_sub_le _ _
    _ ≤ K * ‖∑ i, a i • x i‖ + K * ‖∑ i, a i • x i‖ :=
      add_le_add (hx a (j.val + 1) j.is_lt) (hx a j.val j.is_lt.le)
    _ = _ := by ring

theorem CoefficientBasic.norm_entry_le (hx : CoefficientBasic K x) (j : Fin n) :
    ‖x j‖ ≤ (2 * K) * ‖∑ i, x i‖ := by
  simpa only [one_smul] using hx.norm_term_le (fun _ => 1) j

theorem CoefficientBasic.exists_coordinate_functional (hx : CoefficientBasic K x)
    (hK : 0 ≤ K) (j : Fin n) (hj : x j ≠ 0) :
    ∃ f : E →L[ℝ] ℝ, ‖f‖ ≤ 2 * K / ‖x j‖ ∧
      ∀ i : Fin n, f (x i) = if j = i then 1 else 0 := by
  classical
  let T : (Fin n → ℝ) →ₗ[ℝ] E :=
    { toFun := fun a => ∑ i, a i • x i
      map_add' := by
        intro a b
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro c a
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply] }
  have hjpos : 0 < ‖x j‖ := norm_pos_iff.mpr hj
  have hbound (a : Fin n → ℝ) :
      ‖a j‖ ≤ (2 * K / ‖x j‖) * ‖T a‖ := by
    calc
      ‖a j‖ ≤ (2 * K * ‖T a‖) / ‖x j‖ := by
        apply (le_div_iff₀ hjpos).mpr
        calc
          ‖a j‖ * ‖x j‖ = ‖a j • x j‖ := (norm_smul (a j) (x j)).symm
          _ ≤ 2 * K * ‖T a‖ := hx.norm_term_le a j
      _ = _ := by ring
  have hcoord {a b : Fin n → ℝ} (hab : T a = T b) : a j = b j := by
    have hz : T (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have hh := hbound (a - b)
    rw [hz, norm_zero, mul_zero] at hh
    have heq : (a - b) j = 0 := norm_eq_zero.mp (le_antisymm hh (norm_nonneg _))
    exact sub_eq_zero.mp heq
  let R : Submodule ℝ E := LinearMap.range T
  let c : R → (Fin n → ℝ) := fun z => Classical.choose z.property
  have hc (z : R) : T (c z) = (z : E) := Classical.choose_spec z.property
  let L : R →ₗ[ℝ] ℝ :=
    { toFun := fun z => c z j
      map_add' := by
        intro z w
        have h := hcoord (a := c (z + w)) (b := c z + c w) (by
          rw [hc, map_add, hc, hc]
          rfl)
        exact h
      map_smul' := by
        intro a z
        have h := hcoord (a := c (a • z)) (b := a • c z) (by
          rw [hc, map_smul, hc]
          rfl)
        exact h }
  have hL (z : R) : ‖L z‖ ≤ (2 * K / ‖x j‖) * ‖z‖ := by
    have h := hbound (c z)
    rw [hc] at h
    exact h
  let F : R →L[ℝ] ℝ := L.mkContinuous (2 * K / ‖x j‖) hL
  have hF : ‖F‖ ≤ 2 * K / ‖x j‖ :=
    L.mkContinuous_norm_le (div_nonneg (mul_nonneg (by norm_num) hK) hjpos.le) hL
  obtain ⟨f, hf, hnorm⟩ := exists_extension_norm_eq R F
  refine ⟨f, hnorm.trans_le hF, ?_⟩
  intro i
  have hTi : T (Pi.single i 1) = x i := by simp [T, Pi.single_apply]
  let z : R := ⟨x i, ⟨Pi.single i 1, hTi⟩⟩
  have hcz : c z j = (Pi.single i (1 : ℝ) : Fin n → ℝ) j := hcoord ((hc z).trans hTi.symm)
  calc
    f (x i) = F z := hf z
    _ = c z j := rfl
    _ = (Pi.single i (1 : ℝ) : Fin n → ℝ) j := hcz
    _ = if j = i then 1 else 0 := by simp [Pi.single_apply]

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_TriangularBasic
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

universe u

variable (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]

variable {X}

namespace TriangularSystem

variable {n m : ℕ} {θ : ℝ}

theorem no_longer_of_no_shorter (h : m ≤ n)
    (hm : ¬ Nonempty (TriangularSystem X m θ)) :
    ¬ Nonempty (TriangularSystem X n θ) := by
  rintro ⟨s⟩
  exact hm ⟨s.restrict h⟩

end TriangularSystem

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_CoefficientBlockGain
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ} {K : ℝ} {x : Fin n → E}

theorem CoefficientBasic.triangular_of_large_entries (hx : CoefficientBasic K x)
    (hK : 0 < K) (hS : 0 < ‖∑ i, x i‖)
    (hlarge : ∀ i, ‖∑ j, x j‖ / 2 < ‖x i‖) :
    Nonempty (TriangularSystem E n (1 / (4 * K ^ 2))) := by
  classical
  let S : ℝ := ‖∑ i, x i‖
  have hSpos : 0 < S := hS
  have hxpos (i : Fin n) : 0 < ‖x i‖ :=
    (div_pos hSpos (by norm_num : (0 : ℝ) < 2)).trans (hlarge i)
  choose f hf hpair using fun i =>
    hx.exists_coordinate_functional hK.le i (norm_pos_iff.mp (hxpos i))
  have hfbound (i : Fin n) : ‖f i‖ ≤ 4 * K / S := by
    apply (hf i).trans
    apply (div_le_div_iff₀ (hxpos i) hSpos).mpr
    have hh : S ≤ 2 * ‖x i‖ := by linarith [hlarge i]
    have hm := mul_le_mul_of_nonneg_left hh
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hK.le)
    nlinarith only [hm]
  let v : Fin n → E := fun i => ∑ j, if j.val < i.val + 1 then x j else 0
  have hv (i : Fin n) : ‖v i‖ ≤ K * S :=
    hx.norm_prefix_le (i.val + 1) i.is_lt
  have hfv (i j : Fin n) : f j (v i) = if j ≤ i then 1 else 0 := by
    change f j (∑ k, if k.val < i.val + 1 then x k else 0) = _
    rw [map_sum]
    calc
      _ = ∑ k : Fin n, if k = j then (if j ≤ i then (1 : ℝ) else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hkj : k = j
        · subst k
          have hcmp : j.val < i.val + 1 ↔ j ≤ i := by
            change j.val < i.val + 1 ↔ j.val ≤ i.val
            omega
          by_cases hji : j ≤ i
          · simp [hcmp, hji, hpair]
          · simp [hcmp, hji]
        · have hjk : j ≠ k := Ne.symm hkj
          by_cases hki : k.val < i.val + 1
          · simp only [ite_eq_left hki, hpair, ite_eq_right hjk, ite_eq_right hkj]
          · simp only [ite_eq_right hki, map_zero, ite_eq_right hkj]
      _ = _ := by simp
  have hKS : 0 < K * S := mul_pos hK hSpos
  have hscale : 0 < S / (4 * K) := div_pos hSpos (by positivity)
  refine ⟨{
    vectors := fun i => (K * S)⁻¹ • v i
    functionals := fun j => (S / (4 * K)) • f j
    vectors_bound := ?_
    functionals_bound := ?_
    pairing := ?_ }⟩
  · intro i
    calc
      ‖(K * S)⁻¹ • v i‖ = (K * S)⁻¹ * ‖v i‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hKS)]
      _ ≤ (K * S)⁻¹ * (K * S) :=
        mul_le_mul_of_nonneg_left (hv i) (inv_nonneg.mpr hKS.le)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hKS)
  · intro j
    calc
      ‖(S / (4 * K)) • f j‖ ≤ (S / (4 * K)) * ‖f j‖ := by
        simpa only [Real.norm_eq_abs, abs_of_pos hscale] using
          ContinuousLinearMap.opNorm_smul_le (S / (4 * K)) (f j)
      _ ≤ (S / (4 * K)) * (4 * K / S) :=
        mul_le_mul_of_nonneg_left (hfbound j) hscale.le
      _ = 1 := by field_simp [ne_of_gt hK, ne_of_gt hSpos]
  · intro i j
    change (S / (4 * K)) * f j ((K * S)⁻¹ • v i) = _
    rw [(f j).map_smul, smul_eq_mul, hfv]
    by_cases hji : j ≤ i
    · simp only [ite_eq_left hji, mul_one]
      field_simp [ne_of_gt hK, ne_of_gt hSpos]

    · simp only [ite_eq_right hji, mul_zero]

theorem CoefficientBasic.exists_half_entry_of_no_triangular
    (hx : CoefficientBasic K x) (hK : 0 < K) (hn : 0 < n)
    (hnone : ¬ Nonempty (TriangularSystem E n (1 / (4 * K ^ 2)))) :
    ∃ i : Fin n, ‖x i‖ ≤ (1 / 2 : ℝ) * ‖∑ j, x j‖ := by
  by_contra h
  have hlarge (i : Fin n) : ‖∑ j, x j‖ / 2 < ‖x i‖ := by
    apply lt_of_not_ge
    intro hi
    apply h ⟨i, ?_⟩
    nlinarith
  have hS : 0 < ‖∑ i, x i‖ := by
    by_contra hnpos
    have hz : ‖∑ i, x i‖ = 0 := le_antisymm (le_of_not_gt hnpos) (norm_nonneg _)
    let i : Fin n := ⟨0, hn⟩
    have hb := hx.norm_entry_le i
    have hh := hlarge i
    rw [hz] at hb hh
    nlinarith
  exact hnone (hx.triangular_of_large_entries hK hS hlarge)

theorem FiniteTriangularObstruction.coefficient_half_gain
    (hE : FiniteTriangularObstruction E) {K : ℝ} (hK : 1 < K) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ x : Fin M → E, CoefficientBasic K x →
      ∃ i : Fin M, ‖x i‖ ≤ (1 / 2 : ℝ) * ‖∑ j, x j‖ := by
  have hKpos : 0 < K := lt_trans zero_lt_one hK
  have hden : 0 < 4 * K ^ 2 := by positivity
  have hθpos : 0 < 1 / (4 * K ^ 2) := one_div_pos.mpr hden
  have hθlt : 1 / (4 * K ^ 2) < 1 := by
    apply (div_lt_one hden).mpr
    nlinarith
  obtain ⟨n, hn, hnone⟩ := hE (1 / (4 * K ^ 2)) hθpos hθlt
  let M := max n 2
  have hM : 0 < M := lt_of_lt_of_le (by decide : 0 < 2) (le_max_right n 2)
  have hnoneM : ¬ Nonempty (TriangularSystem E M (1 / (4 * K ^ 2))) :=
    TriangularSystem.no_longer_of_no_shorter (le_max_left n 2) hnone
  refine ⟨M, le_max_right n 2, ?_⟩
  intro x hx
  exact hx.exists_half_entry_of_no_triangular hKpos hM hnoneM

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_CoefficientSequenceOps
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]
variable {n m k : ℕ}

omit sectionNormedSpaceℝE in
theorem sum_univ_eq_sum_embedding [NormedSpace ℝ E] {A B : Type*} [Fintype A] [Fintype B]
    (e : A ↪ B) (f : B → E)
    (hf : ∀ b, (¬ ∃ a, e a = b) → f b = 0) :
    (∑ b, f b) = ∑ a, f (e a) := by
  classical
  calc
    (∑ b, f b) = ∑ b ∈ Finset.univ.map e, f b := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro b _hb hnot
      apply hf b
      rintro ⟨a, rfl⟩
      exact hnot (Finset.mem_map.mpr ⟨a, Finset.mem_univ a, rfl⟩)
    _ = ∑ a, f (e a) := Finset.sum_map _ _ _

theorem sum_extend_smul (e : Fin m ↪ Fin n) (a : Fin m → ℝ) (x : Fin n → E) :
    (∑ i, Function.extend e a (fun _ => 0) i • x i) = ∑ j, a j • x (e j) := by
  classical
  calc
    _ = ∑ j, Function.extend e a (fun _ => 0) (e j) • x (e j) := by
      apply sum_univ_eq_sum_embedding e
      intro i hi
      rw [Function.extend_apply' a (fun _ => 0) i hi, zero_smul]
    _ = _ := by simp only [e.injective.extend_apply]

theorem CoefficientBasic.comp_orderEmbedding {K : ℝ} {x : Fin n → E}
    (hx : CoefficientBasic K x) (e : Fin m ↪o Fin n) :
    CoefficientBasic K (fun i => x (e i)) := by
  classical
  intro a r hr
  let s : ℕ := if h : r < m then (e ⟨r, h⟩).val else n
  have hs : s ≤ n := by
    dsimp [s]
    split
    · exact (e _).is_lt.le
    · exact le_rfl
  have hcut (j : Fin m) : (e j).val < s ↔ j.val < r := by
    by_cases h : r < m
    · dsimp [s]
      rw [dite_eq_left h]
      change e j < e ⟨r, h⟩ ↔ j < ⟨r, h⟩
      exact e.lt_iff_lt
    · dsimp [s]
      rw [dite_eq_right h]
      exact iff_of_true (e j).is_lt (lt_of_lt_of_le j.is_lt (Nat.le_of_not_gt h))
  have hfull := sum_extend_smul e.toEmbedding a x
  have hpref := sum_extend_smul e.toEmbedding a (fun i => if i.val < s then x i else 0)
  simp only [smul_ite, smul_zero] at hpref
  change (∑ i : Fin n, if i.val < s then
    Function.extend e.toEmbedding a (fun _ => 0) i • x i else 0) =
      ∑ j : Fin m, if (e j).val < s then a j • x (e j) else 0 at hpref
  simp only [hcut] at hpref
  have hh := hx (Function.extend e.toEmbedding a (fun _ => 0)) s hs
  rw [hpref, hfull] at hh
  exact hh

theorem CoefficientBasic.equalBlock {K : ℝ} {x : Fin (m * k) → E}
    (hx : CoefficientBasic K x) (j : Fin m) :
    CoefficientBasic K (equalBlock x j) :=
  hx.comp_orderEmbedding (equalBlockOrderEmbedding j)

omit sectionNormedSpaceℝE in
theorem sum_equalBlocks [NormedSpace ℝ E] (x : Fin (m * k) → E) :
    (∑ j : Fin m, equalBlocks x j) = ∑ i : Fin (m * k), x i := by
  change (∑ j : Fin m, ∑ i : Fin k, x (finProdFinEquiv (j, i))) = _
  rw [← Fintype.sum_prod_type']
  exact finProdFinEquiv.sum_comp x

theorem sum_smul_equalBlocks (x : Fin (m * k) → E) (a : Fin m → ℝ) :
    (∑ j : Fin m, a j • equalBlocks x j) =
      ∑ i : Fin (m * k), a (finProdFinEquiv.symm i).1 • x i := by
  simp only [equalBlocks, equalBlock, Finset.smul_sum]
  rw [← Fintype.sum_prod_type']
  simpa only [Equiv.symm_apply_apply] using
    finProdFinEquiv.sum_comp (fun i : Fin (m * k) => a (finProdFinEquiv.symm i).1 • x i)

theorem finProdFinEquiv_prefix_iff (i : Fin (m * k)) (r : ℕ) :
    i.val < r * k ↔ (finProdFinEquiv.symm i).1.val < r := by
  obtain ⟨⟨j, l⟩, rfl⟩ := finProdFinEquiv.surjective i
  simp only [Equiv.symm_apply_apply]
  change l.val + k * j.val < r * k ↔ j.val < r
  constructor
  · intro h
    by_contra hn
    have hmul : r * k ≤ k * j.val := by
      simpa only [Nat.mul_comm] using Nat.mul_le_mul_right k (Nat.le_of_not_gt hn)
    omega
  · intro h
    have hmul : k * j.val + k ≤ r * k := by
      simpa only [Nat.succ_mul, Nat.mul_comm] using
        Nat.mul_le_mul_right k (Nat.succ_le_of_lt h)
    have hl := l.is_lt
    omega

theorem sum_prefix_smul_equalBlocks (x : Fin (m * k) → E) (a : Fin m → ℝ) (r : ℕ) :
    (∑ j : Fin m, if j.val < r then a j • equalBlocks x j else 0) =
      ∑ i : Fin (m * k), if i.val < r * k then
        a (finProdFinEquiv.symm i).1 • x i else 0 := by
  classical
  have h := sum_smul_equalBlocks x (fun j => if j.val < r then a j else 0)
  simp only [ite_smul, zero_smul] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [finProdFinEquiv_prefix_iff]

theorem CoefficientBasic.equalBlocks {K : ℝ} {x : Fin (m * k) → E}
    (hx : CoefficientBasic K x) : CoefficientBasic K (equalBlocks x) := by
  intro a r hr
  rw [sum_prefix_smul_equalBlocks, sum_smul_equalBlocks]
  exact hx (fun i => a (finProdFinEquiv.symm i).1) (r * k) (Nat.mul_le_mul_right k hr)

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_CoefficientBlockIteration
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem coefficientBasic_half_gain_iterate {M : ℕ} {K : ℝ}
    (hgain : ∀ y : Fin M → E, CoefficientBasic K y →
      ∃ i, ‖y i‖ ≤ (1 / 2 : ℝ) * ‖∑ j, y j‖) :
    ∀ k (x : Fin (M ^ k) → E), CoefficientBasic K x →
      ∃ i, ‖x i‖ ≤ (1 / 2 : ℝ) ^ k * ‖∑ j, x j‖ := by
  intro k
  induction k with
  | zero =>
      simp only [Nat.pow_zero]
      intro x hx
      refine ⟨0, ?_⟩
      rw [pow_zero, one_mul]
      exact (congrArg norm (Fin.sum_univ_one x)).ge
  | succ k ih =>
      have hstep :
          ∀ x : Fin (M * M ^ k) → E, CoefficientBasic K x →
            ∃ i, ‖x i‖ ≤
              (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ k * ‖∑ j, x j‖ := by
        intro x hx
        obtain ⟨b, hb⟩ := hgain (equalBlocks x) hx.equalBlocks
        rw [sum_equalBlocks x] at hb
        obtain ⟨i, hi⟩ := ih (equalBlock x b) (hx.equalBlock b)
        have hc : 0 ≤ (1 / 2 : ℝ) ^ k := pow_nonneg (by norm_num) k
        refine ⟨finProdFinEquiv (b, i), ?_⟩
        calc
          ‖x (finProdFinEquiv (b, i))‖ ≤
              (1 / 2 : ℝ) ^ k * ‖equalBlocks x b‖ := hi
          _ ≤ (1 / 2 : ℝ) ^ k * ((1 / 2 : ℝ) * ‖∑ j, x j‖) :=
            mul_le_mul_of_nonneg_left hb hc
          _ = (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ k * ‖∑ j, x j‖ := by ring
      rw [Nat.pow_succ' (m := M) (n := k)]
      simpa only [pow_succ'] using hstep

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_CoefficientConsecutiveBlocks
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n m : ℕ}

theorem sum_smul_consecutiveBlocks (x : Fin n → E) (cuts : Fin (m + 1) → ℕ)
    (a : Fin m → ℝ) :
    (∑ j : Fin m, a j • consecutiveBlocks x cuts j) =
      ∑ i : Fin n, (∑ j : Fin m,
        if cuts j.castSucc ≤ i.val ∧ i.val < cuts j.succ then a j else 0) • x i := by
  simp only [consecutiveBlocks, Finset.smul_sum, smul_ite, smul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [ite_smul, zero_smul]

theorem consecutiveBlocks_cut_iff (cuts : Fin (m + 1) → ℕ)
    (hcuts : Monotone cuts) (j : Fin m) (r : ℕ) (hr : r ≤ m) (i : Fin n)
    (hij : cuts j.castSucc ≤ i.val ∧ i.val < cuts j.succ) :
    i.val < cuts ⟨r, Nat.lt_succ_of_le hr⟩ ↔ j.val < r := by
  constructor
  · intro hi
    by_contra hj
    have hc : cuts ⟨r, Nat.lt_succ_of_le hr⟩ ≤ cuts j.castSucc := by
      apply hcuts
      change r ≤ j.val
      exact Nat.le_of_not_gt hj
    omega
  · intro hj
    have hc : cuts j.succ ≤ cuts ⟨r, Nat.lt_succ_of_le hr⟩ := by
      apply hcuts
      change j.val + 1 ≤ r
      exact Nat.succ_le_of_lt hj
    exact hij.2.trans_le hc

theorem sum_prefix_smul_consecutiveBlocks (x : Fin n → E)
    (cuts : Fin (m + 1) → ℕ) (hcuts : Monotone cuts)
    (a : Fin m → ℝ) (r : ℕ) (hr : r ≤ m) :
    (∑ j : Fin m, if j.val < r then a j • consecutiveBlocks x cuts j else 0) =
      ∑ i : Fin n, if i.val < cuts ⟨r, Nat.lt_succ_of_le hr⟩ then
        (∑ j : Fin m,
          if cuts j.castSucc ≤ i.val ∧ i.val < cuts j.succ then a j else 0) • x i
        else 0 := by
  have hcoeff (i : Fin n) :
      (∑ j : Fin m, if cuts j.castSucc ≤ i.val ∧ i.val < cuts j.succ then
        (if j.val < r then a j else 0) else 0) =
      if i.val < cuts ⟨r, Nat.lt_succ_of_le hr⟩ then
        (∑ j : Fin m, if cuts j.castSucc ≤ i.val ∧ i.val < cuts j.succ then a j else 0)
      else 0 := by
    by_cases hi : i.val < cuts ⟨r, Nat.lt_succ_of_le hr⟩
    · rw [ite_eq_left hi]
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases hij : cuts j.castSucc ≤ i.val ∧ i.val < cuts j.succ
      · have hj := (consecutiveBlocks_cut_iff cuts hcuts j r hr i hij).mp hi
        simp only [ite_eq_left hij, ite_eq_left hj]
      · simp only [ite_eq_right hij]
    · rw [ite_eq_right hi]
      apply Finset.sum_eq_zero
      intro j _hj
      by_cases hij : cuts j.castSucc ≤ i.val ∧ i.val < cuts j.succ
      · have hj : ¬ j.val < r :=
          fun hj => hi ((consecutiveBlocks_cut_iff cuts hcuts j r hr i hij).mpr hj)
        simp only [ite_eq_left hij, ite_eq_right hj]
      · simp only [ite_eq_right hij]
  have h := sum_smul_consecutiveBlocks x cuts (fun j => if j.val < r then a j else 0)
  simp only [ite_smul, zero_smul] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [hcoeff]
  simp only [ite_smul, zero_smul]

theorem CoefficientBasic.consecutiveBlocks {K : ℝ} {x : Fin n → E}
    (hx : CoefficientBasic K x) (cuts : Fin (m + 1) → ℕ)
    (hcuts : Monotone cuts) (hlast : cuts (Fin.last m) ≤ n) :
    CoefficientBasic K (consecutiveBlocks x cuts) := by
  intro a r hr
  rw [sum_prefix_smul_consecutiveBlocks x cuts hcuts a r hr,
    sum_smul_consecutiveBlocks]
  apply hx
  exact (hcuts (show (⟨r, Nat.lt_succ_of_le hr⟩ : Fin (m + 1)) ≤ Fin.last m from hr)).trans hlast

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_CoefficientBlockPartition
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]
variable {n m : ℕ}

omit sectionNormedSpaceℝE in
theorem consecutiveBlocks_eq_prefix_sub [NormedSpace ℝ E] (x : Fin n → E)
    (cuts : Fin (m + 1) → ℕ) (hcuts : Monotone cuts) (j : Fin m) :
    consecutiveBlocks x cuts j =
      (∑ i : Fin n, if i.val < cuts j.succ then x i else 0) -
        ∑ i : Fin n, if i.val < cuts j.castSucc then x i else 0 := by
  have hstep : cuts j.castSucc ≤ cuts j.succ :=
    hcuts (show j.castSucc ≤ j.succ from Nat.le_succ j.val)
  unfold consecutiveBlocks
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hlo : i.val < cuts j.castSucc
  · have hhi : i.val < cuts j.succ := hlo.trans_le hstep
    simp [hlo, hhi, not_le_of_gt hlo]
  · have hlo' : cuts j.castSucc ≤ i.val := Nat.le_of_not_gt hlo
    simp [hlo, hlo']

theorem sum_consecutiveBlocks (x : Fin n → E) (cuts : Fin (m + 1) → ℕ)
    (hcuts : Monotone cuts) (hfirst : cuts 0 = 0)
    (hlast : cuts (Fin.last m) = n) :
    (∑ j : Fin m, consecutiveBlocks x cuts j) = ∑ i : Fin n, x i := by
  let cutSum : Fin (m + 1) → E := fun j =>
    ∑ i : Fin n, if i.val < cuts j then x i else 0
  have hblock (j : Fin m) :
      consecutiveBlocks x cuts j = cutSum j.succ - cutSum j.castSucc :=
    consecutiveBlocks_eq_prefix_sub x cuts hcuts j
  calc
    (∑ j : Fin m, consecutiveBlocks x cuts j) =
        (∑ j : Fin m, cutSum j.succ) - ∑ j : Fin m, cutSum j.castSucc := by
      simp_rw [hblock]
      exact Finset.sum_sub_distrib (s := Finset.univ)
        (fun j : Fin m => cutSum j.succ) (fun j : Fin m => cutSum j.castSucc)
    _ = cutSum (Fin.last m) - cutSum 0 := by
      apply (sub_eq_sub_iff_add_eq_add (a := ∑ j : Fin m, cutSum j.succ)).mpr
      calc
        (∑ j : Fin m, cutSum j.succ) + cutSum 0 =
            cutSum 0 + ∑ j : Fin m, cutSum j.succ := add_comm _ _
        _ = ∑ j : Fin (m + 1), cutSum j := (Fin.sum_univ_succ cutSum).symm
        _ = (∑ j : Fin m, cutSum j.castSucc) + cutSum (Fin.last m) :=
          Fin.sum_univ_castSucc cutSum
        _ = cutSum (Fin.last m) + ∑ j : Fin m, cutSum j.castSucc := add_comm _ _
    _ = ∑ i : Fin n, x i := by simp [cutSum, hfirst, hlast]

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_CoefficientSelectedBlocks
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n m : ℕ}

theorem selectedBlockCuts_zero (e : Fin m ↪o Fin n) (hm : 0 < m) :
    selectedBlockCuts e 0 = 0 := by
  simp [selectedBlockCuts, hm]

theorem monotone_selectedBlockCuts (e : Fin m ↪o Fin n) :
    Monotone (selectedBlockCuts e) := by
  intro a b hab
  change a.val ≤ b.val at hab
  by_cases ha : a.val < m
  · by_cases ha0 : a.val = 0
    · have hz : selectedBlockCuts e a = 0 := by
        simp only [selectedBlockCuts, dite_eq_left ha, ite_eq_left ha0]
      rw [hz]
      exact Nat.zero_le _
    · by_cases hb : b.val < m
      · have hb0 : b.val ≠ 0 := by omega
        simp only [selectedBlockCuts, dite_eq_left ha, dite_eq_left hb,
          ite_eq_right ha0, ite_eq_right hb0]
        exact e.monotone
          (show (⟨a.val, ha⟩ : Fin m) ≤ ⟨b.val, hb⟩ from hab)
      · simp only [selectedBlockCuts, dite_eq_left ha, dite_eq_right hb, ite_eq_right ha0]
        exact (e ⟨a.val, ha⟩).is_lt.le
  · have hb : ¬ b.val < m := by omega
    simp only [selectedBlockCuts, dite_eq_right ha, dite_eq_right hb, le_refl]

theorem selected_mem_block (e : Fin m ↪o Fin n) (j : Fin m) :
    selectedBlockCuts e j.castSucc ≤ (e j).val ∧
      (e j).val < selectedBlockCuts e j.succ := by
  constructor
  · rw [selectedBlockCuts_castSucc]
    split
    · exact Nat.zero_le _
    · exact le_rfl
  · by_cases hj : j.val + 1 < m
    · have hj0 : j.val + 1 ≠ 0 := by omega
      have he : (e j).val < (e ⟨j.val + 1, hj⟩).val :=
        e.strictMono (show j < (⟨j.val + 1, hj⟩ : Fin m) from Nat.lt_succ_self _)
      simpa [selectedBlockCuts, hj, hj0] using he
    · simp [selectedBlockCuts, hj]

theorem sum_selectedConsecutiveBlocks (hm : 0 < m) (e : Fin m ↪o Fin n)
    (x : Fin n → E) :
    (∑ j, selectedConsecutiveBlocks e x j) = ∑ i, x i :=
  sum_consecutiveBlocks x (selectedBlockCuts e) (monotone_selectedBlockCuts e)
    (selectedBlockCuts_zero e hm) (selectedBlockCuts_last e)

theorem CoefficientBasic.selectedConsecutiveBlocks {K : ℝ} {x : Fin n → E}
    (hx : CoefficientBasic K x) (e : Fin m ↪o Fin n) :
    CoefficientBasic K (selectedConsecutiveBlocks e x) :=
  hx.consecutiveBlocks (selectedBlockCuts e) (monotone_selectedBlockCuts e)
    (selectedBlockCuts_last e).le

theorem norm_selected_le_two_mul_block {K : ℝ} {x : Fin n → E}
    (hx : CoefficientBasic K x) (e : Fin m ↪o Fin n) (j : Fin m) :
    ‖x (e j)‖ ≤ (2 * K) * ‖selectedConsecutiveBlocks e x j‖ := by
  classical
  let y : Fin n → E := fun i =>
    if selectedBlockCuts e j.castSucc ≤ i.val ∧ i.val < selectedBlockCuts e j.succ
      then x i else 0
  have hy : CoefficientBasic K y := by
    simpa only [ite_smul, one_smul, zero_smul] using
      hx.smul (fun i => if selectedBlockCuts e j.castSucc ≤ i.val ∧
        i.val < selectedBlockCuts e j.succ then (1 : ℝ) else 0)
  have h := hy.norm_entry_le (e j)
  simpa only [y, ite_eq_left (selected_mem_block e j), selectedConsecutiveBlocks,
    consecutiveBlocks] using h

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_CoefficientThresholdCount
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem coefficientBasic_card_large_lt_pow {M : ℕ} {K : ℝ}
    (hM : 0 < M) (hK : 0 ≤ K)
    (hgain : ∀ y : Fin M → E, CoefficientBasic K y →
      ∃ i, ‖y i‖ ≤ (1 / 2 : ℝ) * ‖∑ j, y j‖)
    {n : ℕ} (x : Fin n → E) (hx : CoefficientBasic K x) (k : ℕ) :
    (Finset.univ.filter (fun i =>
      (2 * K) * (1 / 2 : ℝ) ^ k * ‖∑ j, x j‖ < ‖x i‖)).card < M ^ k := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter (fun i =>
    (2 * K) * (1 / 2 : ℝ) ^ k * ‖∑ j, x j‖ < ‖x i‖)
  by_contra h
  have hcard : M ^ k ≤ s.card := Nat.le_of_not_gt h
  let e : Fin (M ^ k) ↪o Fin n := s.orderEmbOfCardLe hcard
  have he (i : Fin (M ^ k)) :
      (2 * K) * (1 / 2 : ℝ) ^ k * ‖∑ j, x j‖ < ‖x (e i)‖ :=
    (Finset.mem_filter.mp (s.orderEmbOfCardLe_mem hcard i)).2
  let y : Fin (M ^ k) → E := selectedConsecutiveBlocks e x
  have hy : CoefficientBasic K y := hx.selectedConsecutiveBlocks e
  obtain ⟨i, hi⟩ := coefficientBasic_half_gain_iterate hgain k y hy
  have hsum : (∑ j, y j) = ∑ j, x j :=
    sum_selectedConsecutiveBlocks (pow_pos hM k) e x
  rw [hsum] at hi
  have hentry := norm_selected_le_two_mul_block hx e i
  have hbound : ‖x (e i)‖ ≤ (2 * K) * (1 / 2 : ℝ) ^ k * ‖∑ j, x j‖ := by
    calc
      ‖x (e i)‖ ≤ (2 * K) * ‖y i‖ := hentry
      _ ≤ (2 * K) * ((1 / 2 : ℝ) ^ k * ‖∑ j, x j‖) :=
        mul_le_mul_of_nonneg_left hi (mul_nonneg (by norm_num) hK)
      _ = _ := by ring
  exact (not_lt_of_ge hbound) (he i)

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_GeometricThresholdPowerSum
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

theorem pow_le_geometric_threshold_layers {A x : ℝ}
    (hA : 0 ≤ A) (hx : 0 ≤ x) (hxA : x ≤ A) (q L : ℕ) :
    x ^ q ≤ (A * (1 / 2 : ℝ) ^ L) ^ q +
      ∑ k ∈ Finset.range L,
        if A * (1 / 2 : ℝ) ^ (k + 1) < x then
          (A * (1 / 2 : ℝ) ^ k) ^ q else 0 := by
  induction L with
  | zero =>
      simpa using pow_le_pow_left₀ hx hxA q
  | succ L ih =>
      have htail : 0 ≤ (A * (1 / 2 : ℝ) ^ (L + 1)) ^ q :=
        pow_nonneg (mul_nonneg hA (pow_nonneg (by norm_num) _)) _
      have hsum : 0 ≤ ∑ k ∈ Finset.range L,
          if A * (1 / 2 : ℝ) ^ (k + 1) < x then
            (A * (1 / 2 : ℝ) ^ k) ^ q else 0 := by
        apply Finset.sum_nonneg
        intro k hk
        split
        · exact pow_nonneg (mul_nonneg hA (pow_nonneg (by norm_num) _)) _
        · exact le_rfl
      rw [Finset.sum_range_succ]
      by_cases hnew : A * (1 / 2 : ℝ) ^ (L + 1) < x
      · rw [ite_eq_left hnew]
        linarith
      · rw [ite_eq_right hnew]
        have hbound := pow_le_pow_left₀ hx (le_of_not_gt hnew) q
        linarith

theorem nat_mul_half_pow_mul_le_one (n : ℕ) {q : ℕ} (hq : 1 ≤ q) :
    (n : ℝ) * (1 / 2 : ℝ) ^ (n * q) ≤ 1 := by
  have hbase : ∀ m : ℕ, (m : ℝ) * (1 / 2 : ℝ) ^ m ≤ 1 := by
    intro m
    induction m with
    | zero => norm_num
    | succ m ih =>
        have hpow : (1 / 2 : ℝ) ^ m ≤ 1 :=
          pow_le_one₀ (by norm_num) (by norm_num)
        rw [Nat.cast_succ, pow_succ]
        nlinarith
  have hexp : n ≤ n * q := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left n hq
  have hdec : (1 / 2 : ℝ) ^ (n * q) ≤ (1 / 2 : ℝ) ^ n :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hexp
  exact (mul_le_mul_of_nonneg_left hdec (Nat.cast_nonneg n)).trans (hbase n)

theorem sum_pow_le_of_geometric_threshold_count {n M q : ℕ}
    (hq : 1 ≤ q) {A : ℝ} (hA : 0 ≤ A)
    (hratio : (M : ℝ) * (1 / 2 : ℝ) ^ q < 1)
    (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i) (hupper : ∀ i, r i ≤ A)
    (hcount : ∀ k : ℕ,
      (Finset.univ.filter (fun i => A * (1 / 2 : ℝ) ^ k < r i)).card ≤ M ^ k) :
    ∑ i, r i ^ q ≤
      A ^ q * (1 + (M : ℝ) / (1 - (M : ℝ) * (1 / 2 : ℝ) ^ q)) := by
  classical
  let ρ : ℝ := (M : ℝ) * (1 / 2 : ℝ) ^ q
  have hρ0 : 0 ≤ ρ := mul_nonneg (Nat.cast_nonneg M) (pow_nonneg (by norm_num) q)
  have hρ1 : ρ < 1 := hratio
  have hAq : 0 ≤ A ^ q := pow_nonneg hA q
  have hlayer (k : ℕ) :
      (∑ i, if A * (1 / 2 : ℝ) ^ (k + 1) < r i then
        (A * (1 / 2 : ℝ) ^ k) ^ q else 0) ≤
        A ^ q * (M : ℝ) * ρ ^ k := by
    have hk0 : 0 ≤ (A * (1 / 2 : ℝ) ^ k) ^ q :=
      pow_nonneg (mul_nonneg hA (pow_nonneg (by norm_num) k)) q
    calc
      (∑ i, if A * (1 / 2 : ℝ) ^ (k + 1) < r i then
          (A * (1 / 2 : ℝ) ^ k) ^ q else 0) =
          ((Finset.univ.filter (fun i =>
            A * (1 / 2 : ℝ) ^ (k + 1) < r i)).card : ℝ) *
              (A * (1 / 2 : ℝ) ^ k) ^ q := by
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((M ^ (k + 1) : ℕ) : ℝ) * (A * (1 / 2 : ℝ) ^ k) ^ q :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hcount (k + 1))) hk0
      _ = A ^ q * (M : ℝ) * ρ ^ k := by
        dsimp [ρ]
        simp only [Nat.cast_pow, Nat.cast_mul, mul_pow, pow_succ, ← pow_mul, Nat.mul_comm k q]
        ring
  have htail : (n : ℝ) * (A * (1 / 2 : ℝ) ^ n) ^ q ≤ A ^ q := by
    calc
      (n : ℝ) * (A * (1 / 2 : ℝ) ^ n) ^ q =
          A ^ q * ((n : ℝ) * (1 / 2 : ℝ) ^ (n * q)) := by
        rw [mul_pow, ← pow_mul]
        ring
      _ ≤ A ^ q * 1 :=
        mul_le_mul_of_nonneg_left (nat_mul_half_pow_mul_le_one n hq) hAq
      _ = A ^ q := mul_one _
  have hgeom : (∑ k ∈ Finset.range n, ρ ^ k) ≤ 1 / (1 - ρ) := by
    simpa only [Nat.Ico_zero_eq_range, pow_zero] using
      (geom_sum_Ico_le_of_lt_one hρ0 hρ1 (m := 0) (n := n))
  calc
    (∑ i, r i ^ q) ≤
        ∑ i : Fin n, ((A * (1 / 2 : ℝ) ^ n) ^ q +
          ∑ k ∈ Finset.range n,
            if A * (1 / 2 : ℝ) ^ (k + 1) < r i then
              (A * (1 / 2 : ℝ) ^ k) ^ q else 0) := by
      apply Finset.sum_le_sum
      intro i hi
      exact pow_le_geometric_threshold_layers hA (hr i) (hupper i) q n
    _ = (n : ℝ) * (A * (1 / 2 : ℝ) ^ n) ^ q +
        ∑ k ∈ Finset.range n, ∑ i : Fin n,
          if A * (1 / 2 : ℝ) ^ (k + 1) < r i then
            (A * (1 / 2 : ℝ) ^ k) ^ q else 0 := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ A ^ q + ∑ k ∈ Finset.range n, A ^ q * (M : ℝ) * ρ ^ k :=
      add_le_add htail (Finset.sum_le_sum (fun k hk => hlayer k))
    _ = A ^ q + (A ^ q * (M : ℝ)) * ∑ k ∈ Finset.range n, ρ ^ k := by
      rw [Finset.mul_sum]
    _ ≤ A ^ q + (A ^ q * (M : ℝ)) * (1 / (1 - ρ)) :=
      add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hgeom (mul_nonneg hAq (Nat.cast_nonneg M)))
    _ = A ^ q * (1 + (M : ℝ) / (1 - (M : ℝ) * (1 / 2 : ℝ) ^ q)) := by
      dsimp [ρ]
      ring

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_CoefficientLowerPower
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem coefficientBasic_lower_power_of_half_gain {M q : ℕ} {K : ℝ}
    (hM : 0 < M) (hK : 0 ≤ K) (hq : 1 ≤ q)
    (hratio : (M : ℝ) * (1 / 2 : ℝ) ^ q < 1)
    (hgain : ∀ y : Fin M → E, CoefficientBasic K y →
      ∃ i, ‖y i‖ ≤ (1 / 2 : ℝ) * ‖∑ j, y j‖)
    {n : ℕ} (x : Fin n → E) (hx : CoefficientBasic K x) :
    (∑ i, ‖x i‖ ^ q) ≤
      ((2 * K) ^ q * (1 + (M : ℝ) / (1 - (M : ℝ) * (1 / 2 : ℝ) ^ q))) *
        ‖∑ i, x i‖ ^ q := by
  classical
  let A : ℝ := (2 * K) * ‖∑ i, x i‖
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (by norm_num) hK) (norm_nonneg _)
  have hcount (k : ℕ) :
      (Finset.univ.filter (fun i => A * (1 / 2 : ℝ) ^ k < ‖x i‖)).card ≤ M ^ k := by
    have heq : A * (1 / 2 : ℝ) ^ k =
        (2 * K) * (1 / 2 : ℝ) ^ k * ‖∑ i, x i‖ := by dsimp [A]; ring
    rw [heq]
    exact (coefficientBasic_card_large_lt_pow hM hK hgain x hx k).le
  have hsum := sum_pow_le_of_geometric_threshold_count hq hA hratio
    (fun i => ‖x i‖) (fun i => norm_nonneg _) (fun i => hx.norm_entry_le i) hcount
  calc
    (∑ i, ‖x i‖ ^ q) ≤
        A ^ q * (1 + (M : ℝ) / (1 - (M : ℝ) * (1 / 2 : ℝ) ^ q)) := hsum
    _ = _ := by dsimp [A]; rw [mul_pow]; ring

theorem half_gain_power_ratio_lt_one (M : ℕ) :
    (M : ℝ) * (1 / 2 : ℝ) ^ M < 1 := by
  have hp : (M : ℝ) < (2 : ℝ) ^ M := by
    exact_mod_cast M.lt_pow_self (by decide : 1 < 2)
  have hden : (0 : ℝ) < 2 ^ M := pow_pos (by norm_num) M
  have h := (div_lt_one hden).mpr hp
  simpa only [div_pow, one_pow, div_eq_mul_inv, one_mul, inv_pow] using h

theorem FiniteTriangularObstruction.coefficient_lower_power
    (hE : FiniteTriangularObstruction E) {K : ℝ} (hK : 1 < K) :
    ∃ q : ℕ, 2 ≤ q ∧ ∃ D : ℝ, 0 < D ∧
      ∀ (n : ℕ) (x : Fin n → E), CoefficientBasic K x →
        (∑ i, ‖x i‖ ^ q) ≤ D * ‖∑ i, x i‖ ^ q := by
  obtain ⟨M, hM, hgain⟩ := hE.coefficient_half_gain hK
  have hMpos : 0 < M := lt_of_lt_of_le (by decide : 0 < 2) hM
  have hKpos : 0 < K := lt_trans zero_lt_one hK
  have hr := half_gain_power_ratio_lt_one M
  let D : ℝ := (2 * K) ^ M *
    (1 + (M : ℝ) / (1 - (M : ℝ) * (1 / 2 : ℝ) ^ M))
  have hD : 0 < D := by
    have hden : 0 < 1 - (M : ℝ) * (1 / 2 : ℝ) ^ M := sub_pos.mpr hr
    have hfrac : 0 ≤ (M : ℝ) / (1 - (M : ℝ) * (1 / 2 : ℝ) ^ M) :=
      div_nonneg (Nat.cast_nonneg M) hden.le
    exact mul_pos (pow_pos (mul_pos (by norm_num) hKpos) M) (by linarith)
  refine ⟨M, hM, D, hD, ?_⟩
  intro n x hx
  exact coefficientBasic_lower_power_of_half_gain hMpos hKpos.le
    (le_trans (by decide : 1 ≤ 2) hM) hr hgain x hx

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteProbability
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

theorem expect_nonneg (μ : FiniteLaw Ω) {F : Ω → ℝ} (hF : ∀ ω, 0 ≤ F ω) :
    0 ≤ μ.expect F :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (μ.mass_nonneg ω) (hF ω)

theorem expect_mono (μ : FiniteLaw Ω) {F G : Ω → ℝ} (hFG : ∀ ω, F ω ≤ G ω) :
    μ.expect F ≤ μ.expect G :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hFG ω) (μ.mass_nonneg ω)

end FiniteLaw

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteIndependentCopies
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity
namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

theorem prob_not (μ : FiniteLaw Ω) (A : Ω → Prop) :
    μ.prob (fun ω => ¬ A ω) = 1 - μ.prob A := by
  classical
  have hadd : μ.prob A + μ.prob (fun ω => ¬ A ω) = 1 := by
    unfold prob
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ ω, μ.mass ω := by
        apply Finset.sum_congr rfl
        intro ω _
        by_cases h : A ω <;> simp [h]
      _ = 1 := μ.sum_mass
  linarith

theorem independentCopies_prob_rect (μ : FiniteLaw Ω) (m : ℕ)
    (A : Fin m → Ω → Prop) :
    (μ.independentCopies m).prob (fun x => ∀ i, A i (x i)) =
      ∏ i, μ.prob (A i) := by
  classical
  unfold prob
  simp only [independentCopies_mass]
  trans (∑ x : Fin m → Ω, ∏ i, if A i (x i) then μ.mass (x i) else 0)
  · apply Finset.sum_congr rfl
    intro x _
    by_cases hx : ∀ i, A i (x i)
    · simpa only [ite_eq_left hx] using
        (Fintype.prod_ite_zero (p := fun i => A i (x i))
          (f := fun i => μ.mass (x i))).symm
    · simpa only [ite_eq_right hx] using
        (Fintype.prod_ite_zero (p := fun i => A i (x i))
          (f := fun i => μ.mass (x i))).symm
  · exact (Fintype.prod_sum (fun i ω => if A i ω then μ.mass ω else 0)).symm

theorem independentCopies_prob_all (μ : FiniteLaw Ω) (m : ℕ) (A : Ω → Prop) :
    (μ.independentCopies m).prob (fun x => ∀ i, A (x i)) = (μ.prob A) ^ m := by
  simpa using μ.independentCopies_prob_rect m (fun _ => A)

theorem independentCopies_expect_prod (μ : FiniteLaw Ω) (m : ℕ)
    (f : Fin m → Ω → ℝ) :
    (μ.independentCopies m).expect (fun x => ∏ i, f i (x i)) =
      ∏ i, μ.expect (f i) := by
  classical
  unfold expect
  simp only [independentCopies_mass, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i ω => μ.mass ω * f i ω)).symm

theorem independentCopies_expect_coord (μ : FiniteLaw Ω) {m : ℕ}
    (j : Fin m) (f : Ω → ℝ) :
    (μ.independentCopies m).expect (fun x => f (x j)) = μ.expect f := by
  classical
  have h := μ.independentCopies_expect_prod m (fun i ω => if i = j then f ω else 1)
  have hprod (x : Fin m → Ω) : (∏ i, if i = j then f (x i) else 1) = f (x j) := by
    rw [Finset.prod_eq_single j]
    · simp
    · intro i _ hij
      simp only [ite_eq_right hij]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  simp_rw [hprod] at h
  calc
    (μ.independentCopies m).expect (fun x => f (x j)) =
        ∏ i, μ.expect (fun ω => if i = j then f ω else 1) := h
    _ = μ.expect (fun ω => if j = j then f ω else 1) := by
      apply Finset.prod_eq_single j
      · intro i _ hij
        simp only [ite_eq_right hij, expect_const]
      · intro hj
        exact (hj (Finset.mem_univ j)).elim
    _ = μ.expect f := by simp

theorem independentCopies_prob_all_norm_le {E : Type*} [SeminormedAddCommGroup E]
    (μ : FiniteLaw Ω) (m : ℕ) (F : Ω → E) (t : ℝ) :
    (μ.independentCopies m).prob (fun x => ∀ i, ‖F (x i)‖ ≤ t) =
      (1 - μ.prob (fun ω => t < ‖F ω‖)) ^ m := by
  calc
    _ = (μ.prob (fun ω => ‖F ω‖ ≤ t)) ^ m :=
      μ.independentCopies_prob_all m (fun ω => ‖F ω‖ ≤ t)
    _ = _ := by
      have h := μ.prob_not (fun ω => t < ‖F ω‖)
      simpa only [not_lt] using congrArg (fun z : ℝ => z ^ m) h

end FiniteLaw
end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteStoppingTime
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

namespace FinitePartitionFiltration

variable {Ω : Type*} (F : FinitePartitionFiltration Ω)

theorem stopped_atom_and_predictable_eq {τ σ : Ω → ℕ}
    (hτ : F.IsStoppingTime τ) (hσ : F.IsPredictableTime σ)
    (a : Ω) {n : ℕ} (hn : 0 < n)
    (hstrict : ∀ ω, σ ω = n → τ ω < n)
    {ω η : Ω} (hωη : (F.part (n - 1)).r ω η) :
    ((F.stoppedSetoid τ).r ω a ∧ σ ω = n) ↔
      ((F.stoppedSetoid τ).r η a ∧ σ η = n) := by
  have hstep (u v : Ω) (huv : (F.part (n - 1)).r u v)
      (hu : (F.stoppedSetoid τ).r u a ∧ σ u = n) :
      (F.stoppedSetoid τ).r v a ∧ σ v = n := by
    have hv : σ v = n := (hσ n hn huv).mp hu.2
    have htime : τ u ≤ n - 1 := by
      have := hstrict u hu.2
      omega
    have hstop : (F.stoppedSetoid τ).r u v :=
      F.stopped_rel_of_rel_of_le hτ huv htime
    exact ⟨(F.stoppedSetoid τ).trans' ((F.stoppedSetoid τ).symm' hstop) hu.1, hv⟩
  exact ⟨hstep ω η hωη, hstep η ω ((F.part (n - 1)).symm' hωη)⟩

end FinitePartitionFiltration

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteDyadicProbability
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

theorem dyadicPrefix_eq_of_rel {N j : ℕ} {ω η : DyadicWord N} (hj : j ≤ N)
    (h : ((dyadicFiltration N).part j).r ω η) :
    dyadicPrefix ω j hj = dyadicPrefix η j hj := by
  funext i
  exact h ⟨i.val, i.is_lt.trans_le hj⟩ i.is_lt

theorem dyadic_prod_initial (N j : ℕ) (hj : j ≤ N) (a : ℝ) :
    (∏ i : Fin N, if i.val < j then a else 1) = a ^ j := by
  rw [Fin.prod_univ_eq_prod_range (fun i : ℕ => if i < j then a else 1) N]
  induction N with
  | zero =>
      have hj₀ : j = 0 := by omega
      simp [hj₀]
  | succ N ih =>
      rw [Finset.prod_range_succ]
      by_cases hjN : j ≤ N
      · rw [ih hjN, ite_eq_right (not_lt.mpr hjN), mul_one]
      · have hj' : j = N + 1 := by omega
        subst j
        have hprod : (∏ i ∈ Finset.range N, if i < N + 1 then a else 1) = a ^ N := by
          calc
            _ = ∏ _i ∈ Finset.range N, a := by
              apply Finset.prod_congr rfl
              intro i hi
              rw [ite_eq_left ((Finset.mem_range.mp hi).trans (Nat.lt_succ_self N))]
            _ = a ^ N := by simp
        rw [hprod, ite_eq_left (Nat.lt_succ_self N), pow_succ]

theorem dyadicLaw_prob_prefix {N j : ℕ} (hj : j ≤ N) (α : DyadicWord j) :
    (dyadicLaw N).prob (fun ω => dyadicPrefix ω j hj = α) = (dyadicLaw j).mass α := by
  classical
  let A : Fin N → Bool → Prop := fun i b =>
    if hi : i.val < j then b = α ⟨i.val, hi⟩ else True
  have hevent : (fun ω : DyadicWord N => dyadicPrefix ω j hj = α) =
      (fun ω => ∀ i, A i (ω i)) := by
    funext ω
    apply propext
    constructor
    · intro h i
      by_cases hi : i.val < j
      · have heq := congrFun h ⟨i.val, hi⟩
        simpa only [A, dite_eq_left hi, dyadicPrefix] using heq
      · simp only [A, dite_eq_right hi]
    · intro h
      funext i
      have hi : (⟨i.val, i.is_lt.trans_le hj⟩ : Fin N).val < j := i.is_lt
      simpa only [A, dite_eq_left hi, dyadicPrefix] using h ⟨i.val, i.is_lt.trans_le hj⟩
  rw [hevent]
  change (fairBitLaw.independentCopies N).prob (fun ω => ∀ i, A i (ω i)) = _
  rw [FiniteLaw.independentCopies_prob_rect, dyadicLaw_mass]
  calc
    (∏ i, fairBitLaw.prob (A i)) = ∏ i : Fin N, if i.val < j then (2 : ℝ)⁻¹ else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i.val < j
      · simp only [A, dite_eq_left hi, fairBitLaw_prob_eq, ite_eq_left hi]
      · simp only [A, dite_eq_right hi, FiniteLaw.prob_true, ite_eq_right hi]
    _ = (2 : ℝ)⁻¹ ^ j := dyadic_prod_initial N j hj _

theorem FiniteLaw.expect_eq_sum_fiber {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (μ : FiniteLaw Ω) (π : Ω → Ξ) (f : Ξ → ℝ) :
    μ.expect (fun ω => f (π ω)) = ∑ ξ, μ.prob (fun ω => π ω = ξ) * f ξ := by
  classical
  unfold FiniteLaw.expect FiniteLaw.prob
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp only [ite_mul, zero_mul]
  simp

theorem dyadicLaw_expect_prefix {N j : ℕ} (hj : j ≤ N) (f : DyadicWord j → ℝ) :
    (dyadicLaw N).expect (fun ω => f (dyadicPrefix ω j hj)) = (dyadicLaw j).expect f := by
  rw [FiniteLaw.expect_eq_sum_fiber]
  simp_rw [dyadicLaw_prob_prefix hj]
  rfl

theorem dyadicFlip_rel {N : ℕ} (i : Fin N) (ω : DyadicWord N) :
    ((dyadicFiltration N).part i.val).r (dyadicFlip i ω) ω := by
  intro j hj
  apply dyadicFlip_of_ne
  intro hji
  subst j
  exact (Nat.lt_irrefl i.val) hj

@[simp] theorem dyadicFlip_prefix {N : ℕ} (i : Fin N) (ω : DyadicWord N) :
    dyadicPrefix (dyadicFlip i ω) i.val (Nat.le_of_lt i.is_lt) =
      dyadicPrefix ω i.val (Nat.le_of_lt i.is_lt) :=
  dyadicPrefix_eq_of_rel _ (dyadicFlip_rel i ω)

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_DyadicBlockCoordinates
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

theorem dyadicBlock_mass (m N : ℕ) (ω : DyadicWord (m * N)) :
    (dyadicLaw (m * N)).mass ω =
      ((dyadicLaw N).independentCopies m).mass (dyadicBlockEquiv m N ω) := by
  rw [dyadicLaw_mass, FiniteLaw.independentCopies_mass]
  simp only [dyadicLaw_mass, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul, Nat.mul_comm]

theorem dyadicBlock_prob (m N : ℕ) (A : (Fin m → DyadicWord N) → Prop) :
    (dyadicLaw (m * N)).prob (fun ω => A (dyadicBlockEquiv m N ω)) =
      ((dyadicLaw N).independentCopies m).prob A := by
  classical
  unfold FiniteLaw.prob
  simp_rw [dyadicBlock_mass m N]
  exact (dyadicBlockEquiv m N).sum_comp
    (fun x => if A x then ((dyadicLaw N).independentCopies m).mass x else 0)

theorem dyadicBlock_expect (m N : ℕ) (f : (Fin m → DyadicWord N) → ℝ) :
    (dyadicLaw (m * N)).expect (fun ω => f (dyadicBlockEquiv m N ω)) =
      ((dyadicLaw N).independentCopies m).expect f := by
  unfold FiniteLaw.expect
  simp_rw [dyadicBlock_mass m N]
  exact (dyadicBlockEquiv m N).sum_comp
    (fun x => ((dyadicLaw N).independentCopies m).mass x * f x)

theorem dyadicBlock_expect_coord {m N : ℕ} (b : Fin m) (f : DyadicWord N → ℝ) :
    (dyadicLaw (m * N)).expect (fun ω => f (dyadicBlockEquiv m N ω b)) =
      (dyadicLaw N).expect f :=
  (dyadicBlock_expect m N (fun x => f (x b))).trans
    ((dyadicLaw N).independentCopies_expect_coord b f)

theorem dyadicBlockPrefix_prefix {m N : ℕ} (j : Fin (m * N))
    (ω : DyadicWord (m * N)) :
    dyadicBlockPrefix j (dyadicPrefix ω j.val (Nat.le_of_lt j.is_lt)) =
      dyadicPrefix (dyadicBlockEquiv m N ω
        ((finProdFinEquiv (m := m) (n := N)).symm j).1)
        ((finProdFinEquiv (m := m) (n := N)).symm j).2.val
        (Nat.le_of_lt ((finProdFinEquiv (m := m) (n := N)).symm j).2.is_lt) := by
  funext k
  apply congrArg ω
  apply Fin.ext
  rfl

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_DyadicTree
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

universe u

namespace DyadicTree

variable {X : Type u}

theorem pad_full (n : ℕ) (t : DyadicTree X) (h : height t ≤ n) :
    Full n (pad n t) := by
  induction n generalizing t with
  | zero =>
      cases t with
      | leaf x => trivial
      | node t s => simp [height] at h
  | succ n ih =>
      cases t with
      | leaf x =>
          exact ⟨ih (leaf x) (Nat.zero_le n), ih (leaf x) (Nat.zero_le n)⟩
      | node t s =>
          have hm : max (height t) (height s) ≤ n := Nat.le_of_succ_le_succ h
          exact ⟨ih t ((le_max_left _ _).trans hm),
            ih s ((le_max_right _ _).trans hm)⟩

end DyadicTree
end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_PowerConvexity
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem uniformConvex_of_symmetric_power
    (p : Seminorm ℝ E) (q c : ℝ) (hq : 0 < q) (hc : 0 < c) (hc_one : c ≤ 1)
    (hpower : ∀ x y : E, (p x) ^ q + c * (p y) ^ q ≤
      ((p (x + y)) ^ q + (p (x - y)) ^ q) / 2) : UniformConvex p := by
  intro ε hε hε_two
  let d : ℝ := c * (ε / 2) ^ q
  have hd : 0 < d := mul_pos hc (Real.rpow_pos_of_pos (half_pos hε) q)
  have hehalf : ε / 2 ≤ 1 := by linarith only [hε_two]
  have hepow : (ε / 2) ^ q ≤ 1 := by
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow (half_pos hε).le hehalf hq.le
  have hd_one : d ≤ 1 := by
    calc
      c * (ε / 2) ^ q ≤ c * 1 := mul_le_mul_of_nonneg_left hepow hc.le
      _ ≤ 1 := by simpa only [mul_one] using hc_one
  let r : ℝ := 1 - d
  have hr : 0 ≤ r := sub_nonneg.mpr hd_one
  have hr_one : r < 1 := by dsimp [r]; linarith only [hd]
  have hrpow : r ^ (1 / q) < 1 := by
    simpa only [Real.one_rpow] using
      Real.rpow_lt_rpow hr hr_one (one_div_pos.mpr hq)
  let δ : ℝ := 1 - r ^ (1 / q)
  refine ⟨δ, sub_pos.mpr hrpow, ?_⟩
  intro x y hx hy hsep
  let z : E := (1 / 2 : ℝ) • (x + y)
  let w : E := (1 / 2 : ℝ) • (x - y)
  have hz : z + w = x := by dsimp [z, w]; module
  have hw : z - w = y := by dsimp [z, w]; module
  have hs := hpower z w
  rw [hz, hw] at hs
  have hxpow : (p x) ^ q ≤ 1 := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow (apply_nonneg p x) hx hq.le
  have hypow : (p y) ^ q ≤ 1 := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow (apply_nonneg p y) hy hq.le
  have hwvalue : p w = p (x - y) / 2 := by
    dsimp [w]
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    ring
  have hwlower : ε / 2 ≤ p w := by rw [hwvalue]; linarith only [hsep]
  have hwpow := Real.rpow_le_rpow (half_pos hε).le hwlower hq.le
  have hcwpow := mul_le_mul_of_nonneg_left hwpow hc.le
  have hzbound : (p z) ^ q ≤ r := by
    dsimp [r, d]
    linarith only [hs, hxpow, hypow, hcwpow]
  have hroot : p z ≤ r ^ (1 / q) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg (apply_nonneg p z) q)
      hzbound (one_div_pos.mpr hq).le
    have hexp : q * (1 / q) = (1 : ℝ) := by field_simp [hq.ne']
    rw [← Real.rpow_mul (apply_nonneg p z), hexp, Real.rpow_one] at h
    exact h
  change p z ≤ 1 - δ
  dsimp [δ]
  linarith only [hroot]

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_DyadicConvexPotential
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.Renormed.instAddCommGroup _root_.OAI.MarkovSuperreflexivity.Renormed.instModuleReal _root_.OAI.MarkovSuperreflexivity.Renormed.instNorm _root_.OAI.MarkovSuperreflexivity.Renormed.instNormedAddCommGroup _root_.OAI.MarkovSuperreflexivity.Renormed.instNormedSpaceReal _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {E}

namespace DyadicConvex

open DyadicTree

theorem seminorm_rpow {q A : ℝ} (hq : 0 < q) (hA : 0 < A)
    (hc : FiniteDyadicCotype E q A) (x : E) :
    (seminorm hq hA hc x) ^ q = potential q A⁻¹ x :=
  potentialRoot_rpow q hq (potential q A⁻¹) (potential_nonneg hA hc) x

theorem seminorm_symmetric_original {q A : ℝ} (hq : 0 < q) (hA : 0 < A)
    (hc : FiniteDyadicCotype E q A) (x y : E) :
    (seminorm hq hA hc x) ^ q + A⁻¹ * ‖y‖ ^ q ≤
      ((seminorm hq hA hc (x + y)) ^ q + (seminorm hq hA hc (x - y)) ^ q) / 2 := by
  have h := potential_midpoint hA hc (x + y) (x - y)
  have hx : (2 : ℝ)⁻¹ • ((x + y) + (x - y)) = x := by module
  have hy : (2 : ℝ)⁻¹ • ((x + y) - (x - y)) = y := by module
  rw [hx, hy] at h
  simpa only [seminorm_rpow hq hA hc] using h

theorem seminorm_symmetric {q A : ℝ} (hq : 0 < q) (hA : 0 < A)
    (hc : FiniteDyadicCotype E q A) (x y : E) :
    (seminorm hq hA hc x) ^ q + A⁻¹ * (seminorm hq hA hc y) ^ q ≤
      ((seminorm hq hA hc (x + y)) ^ q + (seminorm hq hA hc (x - y)) ^ q) / 2 := by
  have h := seminorm_symmetric_original hq hA hc x y
  have hnonneg : 0 ≤ seminorm hq hA hc y :=
    potentialRoot_nonneg q (potential q A⁻¹) (potential_nonneg hA hc) y
  have hpow := Real.rpow_le_rpow hnonneg (seminorm_upper hq hA hc y) hq.le
  have hm := mul_le_mul_of_nonneg_left hpow (inv_nonneg.mpr hA.le)
  linarith only [h, hm]

theorem equivalentNorm_uniformConvex {q A : ℝ} (hq : 0 < q) (hA : 1 ≤ A)
    (hc : FiniteDyadicCotype E q A) :
    UniformConvex (equivalentNorm hq (zero_lt_one.trans_le hA) hc).p := by
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hβone : A⁻¹ ≤ 1 := by
    simpa only [one_div] using (div_le_one hApos).mpr hA
  exact uniformConvex_of_symmetric_power (seminorm hq hApos hc) q A⁻¹ hq
    (inv_pos.mpr hApos) hβone (seminorm_symmetric hq hApos hc)

end DyadicConvex

theorem hasEquivalentUCNorm_of_finiteDyadicCotype {q A : ℝ}
    (hq : 2 ≤ q) (hA : 1 ≤ A) (hc : FiniteDyadicCotype E q A) :
    HasEquivalentUCNorm E := by
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hq
  have hApos : 0 < A := zero_lt_one.trans_le hA
  exact ⟨DyadicConvex.equivalentNorm hqpos hApos hc,
    DyadicConvex.equivalentNorm_uniformConvex hqpos hA hc⟩

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FinitePowerIntegrals
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set

namespace MarkovSuperreflexivity

theorem lowerPowerKernel_eq_indicator (s r : ℝ) :
    lowerPowerKernel s r =
      (Ioo (0 : ℝ) r).indicator (fun t => t ^ (s - 1)) := by
  funext t
  simp only [lowerPowerKernel, Set.indicator, Set.mem_Ioo]

theorem upperPowerKernel_eq_indicator {s r : ℝ} (hr : 0 < r) :
    upperPowerKernel s r =
      (Ici r).indicator (fun t => t ^ (-s - 1)) := by
  funext t
  by_cases hrt : r ≤ t
  · have ht : 0 < t := hr.trans_le hrt
    simp [upperPowerKernel, Set.indicator, hrt, ht]
  · simp [upperPowerKernel, Set.indicator, hrt]

theorem integrable_lowerPowerKernel {s r : ℝ} (hs : 0 < s) (hr : 0 ≤ r) :
    Integrable (lowerPowerKernel s r) := by
  rw [lowerPowerKernel_eq_indicator]
  have hp : -1 < s - 1 := by linarith
  have hi : IntervalIntegrable (fun t : ℝ => t ^ (s - 1)) volume 0 r :=
    intervalIntegral.intervalIntegrable_rpow' hp
  exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le hr).mp hi).integrable_indicator
    measurableSet_Ioo

theorem integral_lowerPowerKernel {s r : ℝ} (hs : 0 < s) (hr : 0 ≤ r) :
    (∫ t, lowerPowerKernel s r t) = r ^ s / s := by
  rw [lowerPowerKernel_eq_indicator, integral_indicator measurableSet_Ioo,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr]
  simpa only [sub_add_cancel, Real.zero_rpow hs.ne', sub_zero] using
    (_root_.integral_rpow (a := 0) (b := r) (r := s - 1)
      (Or.inl (by linarith : -1 < s - 1)))

theorem integrable_upperPowerKernel {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    Integrable (upperPowerKernel s r) := by
  rw [upperPowerKernel_eq_indicator hr]
  have hi : IntegrableOn (fun t : ℝ => t ^ (-s - 1)) (Ioi r) :=
    integrableOn_Ioi_rpow_of_lt (by linarith : -s - 1 < -1) hr
  exact ((integrableOn_Ici_iff_integrableOn_Ioi
    (f := fun t : ℝ => t ^ (-s - 1)) (b := r) (by finiteness)).mpr hi).integrable_indicator
    measurableSet_Ici

theorem integral_upperPowerKernel {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    (∫ t, upperPowerKernel s r t) = r ^ (-s) / s := by
  rw [upperPowerKernel_eq_indicator hr, integral_indicator measurableSet_Ici,
    integral_Ici_eq_integral_Ioi]
  simpa only [sub_add_cancel, neg_div_neg_eq] using
    (integral_Ioi_rpow_of_lt (a := -s - 1) (c := r)
      (by linarith : -s - 1 < -1) hr)

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteMarcinkiewicz
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped BigOperators

namespace MarkovSuperreflexivity

variable {I Ω E F : Type*} [sectionFintypeI : Fintype I] [Fintype Ω]
  [NormedAddCommGroup E] [NormedAddCommGroup F]

omit sectionFintypeI in
theorem largeCut_add_smallCut [Fintype I] (φ : I → E) (t : ℝ) :
    largeCut φ t + smallCut φ t = φ := by
  funext i
  simp only [Pi.add_apply, largeCut, smallCut]
  split_ifs <;> simp

theorem finiteTail_add_le (ν : Ω → ℝ) (hν : ∀ ω, 0 ≤ ν ω)
    (f g : Ω → F) (t : ℝ) :
    finiteTail ν (f + g) t ≤ finiteTail ν f (t / 2) + finiteTail ν g (t / 2) := by
  classical
  unfold finiteTail
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  change (if t < ‖f ω + g ω‖ then ν ω else 0) ≤
    (if t / 2 < ‖f ω‖ then ν ω else 0) +
      (if t / 2 < ‖g ω‖ then ν ω else 0)
  by_cases h : t < ‖f ω + g ω‖
  · have hpart : t / 2 < ‖f ω‖ ∨ t / 2 < ‖g ω‖ := by
      by_cases hf : t / 2 < ‖f ω‖
      · exact Or.inl hf
      by_cases hg : t / 2 < ‖g ω‖
      · exact Or.inr hg
      have hf' := le_of_not_gt hf
      have hg' := le_of_not_gt hg
      have htriangle := norm_add_le (f ω) (g ω)
      exfalso
      linarith
    rcases hpart with hf | hg
    · simp only [ite_eq_left h, ite_eq_left hf]
      split_ifs <;> linarith [hν ω]
    · simp only [ite_eq_left h, ite_eq_left hg]
      split_ifs <;> linarith [hν ω]
  · simp only [ite_eq_right h]
    split_ifs <;> linarith [hν ω]

section Linear

variable [NormedSpace ℝ E] [NormedSpace ℝ F]

theorem finiteTail_split_weak (w : I → ℝ) (ν : Ω → ℝ) (hν : ∀ ω, 0 ≤ ν ω)
    (T : (I → E) →ₗ[ℝ] (Ω → F)) {p₀ p₁ A₀ A₁ : ℝ}
    (h₀ : FiniteWeakType w ν T p₀ A₀) (h₁ : FiniteWeakType w ν T p₁ A₁)
    (φ : I → E) {t : ℝ} (ht : 0 < t) :
    finiteTail ν (T φ) t ≤
      (A₀ / (t / 2)) ^ p₀ * finiteMoment w p₀ (largeCut φ t) +
      (A₁ / (t / 2)) ^ p₁ * finiteMoment w p₁ (smallCut φ t) := by
  have hsplit : T φ = T (largeCut φ t) + T (smallCut φ t) := by
    rw [← map_add, largeCut_add_smallCut]
  rw [hsplit]
  exact (finiteTail_add_le ν hν _ _ t).trans
    (add_le_add (h₀ _ _ (half_pos ht)) (h₁ _ _ (half_pos ht)))

end Linear

theorem integrable_largeMomentKernel {p q r : ℝ} (hqp : q < p) (hr : 0 ≤ r) :
    Integrable (largeMomentKernel p q r) :=
  (integrable_lowerPowerKernel (sub_pos.mpr hqp) hr).const_mul _

theorem integral_largeMomentKernel {p q r : ℝ}
    (hp : 0 < p) (hqp : q < p) (hr : 0 ≤ r) :
    (∫ t, largeMomentKernel p q r t) = r ^ p / (p - q) := by
  simp only [largeMomentKernel, integral_const_mul,
    integral_lowerPowerKernel (sub_pos.mpr hqp) hr]
  have hsum : q + (p - q) ≠ 0 := by linarith
  rw [← mul_div_assoc, ← Real.rpow_add' hr hsum]
  congr 1
  congr 1
  ring

theorem integrable_smallMomentKernel {p q r : ℝ}
    (hq : 0 < q) (hpq : p < q) (hr : 0 ≤ r) :
    Integrable (smallMomentKernel p q r) := by
  by_cases hr₀ : r = 0
  · subst r
    have hz : smallMomentKernel p q 0 = fun _ : ℝ => 0 := by
      funext t
      simp only [smallMomentKernel, Real.zero_rpow hq.ne', zero_mul]
    rw [hz]
    exact integrable_zero ℝ ℝ volume
  have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr₀)
  exact (integrable_upperPowerKernel (sub_pos.mpr hpq) hrpos).const_mul _

theorem integral_smallMomentKernel {p q r : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hpq : p < q) (hr : 0 ≤ r) :
    (∫ t, smallMomentKernel p q r t) = r ^ p / (q - p) := by
  by_cases hr₀ : r = 0
  · simp [smallMomentKernel, hr₀, Real.zero_rpow hq.ne', Real.zero_rpow hp.ne']
  have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr₀)
  simp only [smallMomentKernel, integral_const_mul,
    integral_upperPowerKernel (sub_pos.mpr hpq) hrpos]
  rw [← mul_div_assoc, ← Real.rpow_add hrpos]
  congr 1
  congr 1
  ring

theorem integrable_finiteLayerKernel (ν : Ω → ℝ) {p : ℝ} (hp : 0 < p) (f : Ω → F) :
    Integrable (finiteLayerKernel ν p f) :=
  (integrable_finsetSum _ (fun ω _ =>
    (integrable_lowerPowerKernel hp (norm_nonneg (f ω))).const_mul (ν ω))).const_mul p

theorem integral_finiteLayerKernel (ν : Ω → ℝ) {p : ℝ} (hp : 0 < p) (f : Ω → F) :
    (∫ t, finiteLayerKernel ν p f t) = finiteMoment ν p f := by
  classical
  change (∫ t : ℝ, p * ∑ ω, ν ω * lowerPowerKernel p ‖f ω‖ t) = finiteMoment ν p f
  rw [integral_const_mul, integral_finsetSum _ (fun ω _ =>
    (integrable_lowerPowerKernel hp (norm_nonneg (f ω))).const_mul (ν ω))]
  simp_rw [integral_const_mul, integral_lowerPowerKernel hp (norm_nonneg _)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  field_simp [hp.ne']

theorem finiteLayerKernel_eq_of_pos (ν : Ω → ℝ) (p : ℝ) (f : Ω → F)
    {t : ℝ} (ht : 0 < t) :
    finiteLayerKernel ν p f t = p * t ^ (p - 1) * finiteTail ν f t := by
  classical
  simp only [finiteLayerKernel, finiteTail, lowerPowerKernel, ht, true_and]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> ring

theorem integrable_finiteLargeKernel (w : I → ℝ) {p q : ℝ}
    (hqp : q < p) (φ : I → E) : Integrable (finiteLargeKernel w p q φ) :=
  integrable_finsetSum _ (fun i _ =>
    (integrable_largeMomentKernel hqp (norm_nonneg (φ i))).const_mul (w i))

theorem integrable_finiteSmallKernel (w : I → ℝ) {p q : ℝ}
    (hq : 0 < q) (hpq : p < q) (φ : I → E) : Integrable (finiteSmallKernel w p q φ) :=
  integrable_finsetSum _ (fun i _ =>
    (integrable_smallMomentKernel hq hpq (norm_nonneg (φ i))).const_mul (w i))

theorem integral_finiteLargeKernel (w : I → ℝ) {p q : ℝ}
    (hp : 0 < p) (hqp : q < p) (φ : I → E) :
    (∫ t, finiteLargeKernel w p q φ t) = finiteMoment w p φ / (p - q) := by
  classical
  change (∫ t : ℝ, ∑ i, w i * largeMomentKernel p q ‖φ i‖ t) =
    finiteMoment w p φ / (p - q)
  rw [integral_finsetSum _ (fun i _ =>
    (integrable_largeMomentKernel hqp (norm_nonneg (φ i))).const_mul (w i))]
  simp_rw [integral_const_mul, integral_largeMomentKernel hp hqp (norm_nonneg _)]
  simp only [finiteMoment, Finset.sum_div, mul_div_assoc]

theorem integral_finiteSmallKernel (w : I → ℝ) {p q : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hpq : p < q) (φ : I → E) :
    (∫ t, finiteSmallKernel w p q φ t) = finiteMoment w p φ / (q - p) := by
  classical
  change (∫ t : ℝ, ∑ i, w i * smallMomentKernel p q ‖φ i‖ t) =
    finiteMoment w p φ / (q - p)
  rw [integral_finsetSum _ (fun i _ =>
    (integrable_smallMomentKernel hq hpq (norm_nonneg (φ i))).const_mul (w i))]
  simp_rw [integral_const_mul, integral_smallMomentKernel hp hq hpq (norm_nonneg _)]
  simp only [finiteMoment, Finset.sum_div, mul_div_assoc]

theorem weakThresholdFactor {A t : ℝ} (hA : 0 ≤ A) (ht : 0 < t) (q : ℝ) :
    (A / (t / 2)) ^ q = (2 * A) ^ q * t ^ (-q) := by
  have heq : A / (t / 2) = (2 * A) / t := by field_simp [ht.ne']
  rw [heq, Real.div_rpow (mul_nonneg (by norm_num) hA) ht.le,
    Real.rpow_neg ht.le, div_eq_mul_inv]

theorem largeCut_weighted_kernel (w : I → ℝ) (φ : I → E) (p : ℝ)
    {q A t : ℝ} (hq : 0 < q) (hA : 0 ≤ A) (ht : 0 < t) :
    t ^ (p - 1) * ((A / (t / 2)) ^ q * finiteMoment w q (largeCut φ t)) =
      (2 * A) ^ q * finiteLargeKernel w p q φ t := by
  classical
  have hpows : t ^ (p - q - 1) = t ^ (p - 1) * t ^ (-q) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  rw [weakThresholdFactor hA ht q]
  simp only [finiteMoment, finiteLargeKernel]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : t < ‖φ i‖
  · simp only [largeCut, largeMomentKernel, lowerPowerKernel,
      ht, hi, and_self, ite_true]
    rw [hpows]
    ring
  · simp [largeCut, hi, largeMomentKernel, lowerPowerKernel, ht, Real.zero_rpow hq.ne']

theorem smallCut_weighted_kernel (w : I → ℝ) (φ : I → E) (p : ℝ)
    {q A t : ℝ} (hq : 0 < q) (hA : 0 ≤ A) (ht : 0 < t) :
    t ^ (p - 1) * ((A / (t / 2)) ^ q * finiteMoment w q (smallCut φ t)) =
      (2 * A) ^ q * finiteSmallKernel w p q φ t := by
  classical
  have hpows : t ^ (p - q - 1) = t ^ (p - 1) * t ^ (-q) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  rw [weakThresholdFactor hA ht q]
  simp only [finiteMoment, finiteSmallKernel]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : t < ‖φ i‖
  · simp [smallCut, hi, smallMomentKernel, upperPowerKernel, ht,
      not_le.mpr hi, Real.zero_rpow hq.ne']
  · have hir : ‖φ i‖ ≤ t := le_of_not_gt hi
    simp only [smallCut, ite_eq_right hi, smallMomentKernel, upperPowerKernel,
      ht, hir, and_self, ite_true, neg_sub]
    rw [hpows]
    ring

variable [NormedSpace ℝ E] [NormedSpace ℝ F]

theorem finiteLayerKernel_le (w : I → ℝ) (ν : Ω → ℝ) (hν : ∀ ω, 0 ≤ ν ω)
    (T : (I → E) →ₗ[ℝ] (Ω → F)) {p₀ p p₁ A₀ A₁ : ℝ}
    (hp₀ : 0 < p₀) (hp : 0 < p) (hp₁ : 0 < p₁)
    (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (h₀ : FiniteWeakType w ν T p₀ A₀) (h₁ : FiniteWeakType w ν T p₁ A₁)
    (φ : I → E) (t : ℝ) :
    finiteLayerKernel ν p (T φ) t ≤
      p * (2 * A₀) ^ p₀ * finiteLargeKernel w p p₀ φ t +
      p * (2 * A₁) ^ p₁ * finiteSmallKernel w p p₁ φ t := by
  by_cases ht : 0 < t
  · rw [finiteLayerKernel_eq_of_pos ν p (T φ) ht]
    calc
      p * t ^ (p - 1) * finiteTail ν (T φ) t ≤
          p * t ^ (p - 1) *
            ((A₀ / (t / 2)) ^ p₀ * finiteMoment w p₀ (largeCut φ t) +
             (A₁ / (t / 2)) ^ p₁ * finiteMoment w p₁ (smallCut φ t)) :=
        mul_le_mul_of_nonneg_left (finiteTail_split_weak w ν hν T h₀ h₁ φ ht)
          (mul_nonneg hp.le (Real.rpow_nonneg ht.le _))
      _ = p * (t ^ (p - 1) *
            ((A₀ / (t / 2)) ^ p₀ * finiteMoment w p₀ (largeCut φ t))) +
          p * (t ^ (p - 1) *
            ((A₁ / (t / 2)) ^ p₁ * finiteMoment w p₁ (smallCut φ t))) := by ring
      _ = p * (2 * A₀) ^ p₀ * finiteLargeKernel w p p₀ φ t +
          p * (2 * A₁) ^ p₁ * finiteSmallKernel w p p₁ φ t := by
        rw [largeCut_weighted_kernel w φ p hp₀ hA₀ ht,
          smallCut_weighted_kernel w φ p hp₁ hA₁ ht]
        ring
  · simp [finiteLayerKernel, finiteLargeKernel, finiteSmallKernel,
      largeMomentKernel, smallMomentKernel, lowerPowerKernel, upperPowerKernel, ht]

theorem finite_marcinkiewicz
    (w : I → ℝ) (_hw : ∀ i, 0 ≤ w i) (ν : Ω → ℝ) (hν : ∀ ω, 0 ≤ ν ω)
    (T : (I → E) →ₗ[ℝ] (Ω → F)) {p₀ p p₁ A₀ A₁ : ℝ}
    (hp₀ : 0 < p₀) (hp₀p : p₀ < p) (hpp₁ : p < p₁)
    (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (h₀ : FiniteWeakType w ν T p₀ A₀) (h₁ : FiniteWeakType w ν T p₁ A₁)
    (φ : I → E) :
    finiteMoment ν p (T φ) ≤
      (p * ((2 * A₀) ^ p₀ / (p - p₀) + (2 * A₁) ^ p₁ / (p₁ - p))) *
        finiteMoment w p φ := by
  have hp : 0 < p := hp₀.trans hp₀p
  have hp₁ : 0 < p₁ := hp.trans hpp₁
  have hlo := integrable_finiteLargeKernel w hp₀p φ
  have hhi := integrable_finiteSmallKernel w hp₁ hpp₁ φ
  have hbound := integral_mono (integrable_finiteLayerKernel ν hp (T φ))
    ((hlo.const_mul (p * (2 * A₀) ^ p₀)).add
      (hhi.const_mul (p * (2 * A₁) ^ p₁)))
    (finiteLayerKernel_le w ν hν T hp₀ hp hp₁ hA₀ hA₁ h₀ h₁ φ)
  change (∫ t : ℝ, finiteLayerKernel ν p (T φ) t) ≤
    ∫ t : ℝ, p * (2 * A₀) ^ p₀ * finiteLargeKernel w p p₀ φ t +
      p * (2 * A₁) ^ p₁ * finiteSmallKernel w p p₁ φ t at hbound
  rw [integral_finiteLayerKernel ν hp (T φ),
    integral_add (hlo.const_mul _) (hhi.const_mul _),
    integral_const_mul, integral_const_mul,
    integral_finiteLargeKernel w hp hp₀p φ,
    integral_finiteSmallKernel w hp hp₁ hpp₁ φ] at hbound
  convert hbound using 1 ; ring

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteMartingaleBasic
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

variable {Ω E : Type*} [sectionFintypeΩ : Fintype Ω]
variable [NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]

theorem finiteDifference_telescope (M : ℕ → Ω → E) (n : ℕ) (ω : Ω) :
    M n ω = M 0 ω + ∑ j ∈ Finset.range n, finiteDifference M (j + 1) ω := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, finiteDifference_succ M n ω]
    rw [← add_assoc, ← ih]
    abel

theorem hasZeroConditionalSum_zero (μ : FiniteLaw Ω) (P : Setoid Ω) :
    HasZeroConditionalSum μ P (fun _ => (0 : E)) := by
  classical
  intro a
  simp

theorem HasZeroConditionalSum.predictable_smul {μ : FiniteLaw Ω} {P : Setoid Ω}
    {f : Ω → E} (hf : HasZeroConditionalSum μ P f) (c : Ω → ℝ)
    (hc : ∀ {ω η}, P.r ω η → c ω = c η) :
    HasZeroConditionalSum μ P (fun ω => c ω • f ω) := by
  classical
  intro a
  calc
    _ = c a • ∑ ω, if P.r ω a then μ.mass ω • f ω else 0 := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases h : P.r ω a
      · simp only [ite_eq_left h, hc h]
        rw [smul_smul, smul_smul, mul_comm]
      · simp [h]
    _ = 0 := by rw [hf a, smul_zero]

theorem HasZeroConditionalSum.indicator {μ : FiniteLaw Ω} {P : Setoid Ω}
    {f : Ω → E} (hf : HasZeroConditionalSum μ P f) (A : Ω → Prop)
    (hA : ∀ {ω η}, P.r ω η → (A ω ↔ A η)) :
    HasZeroConditionalSum μ P (fun ω => if A ω then f ω else 0) := by
  classical
  have h := hf.predictable_smul (fun ω => if A ω then (1 : ℝ) else 0) (by
    intro ω η hωη
    simp only [hA hωη])
  simpa only [ite_smul, one_smul, zero_smul] using h

namespace FinitePartitionFiltration

theorem IsMartingaleUpTo.difference_adapted {F : FinitePartitionFiltration Ω}
    {μ : FiniteLaw Ω} {M : ℕ → Ω → E} {N j : ℕ}
    (hM : F.IsMartingaleUpTo μ M N) (hj : j ≤ N) :
    F.AdaptedAt j (finiteDifference M j) := by
  unfold AdaptedAt
  intro ω η hωη
  by_cases hj0 : j = 0
  · subst j
    simpa only [finiteDifference_zero] using hM.1 0 hj hωη
  · simp only [finiteDifference, ite_eq_right hj0]
    rw [hM.1 j hj hωη,
      hM.1 (j - 1) ((Nat.sub_le j 1).trans hj) (F.refines (Nat.sub_le j 1) hωη)]

end FinitePartitionFiltration

omit sectionNormedSpaceℝE in
theorem finiteL2Norm_nonneg [NormedSpace ℝ E] (μ : FiniteLaw Ω) (f : Ω → E) :
    0 ≤ finiteL2Norm μ f := Real.sqrt_nonneg _

omit sectionNormedSpaceℝE in
theorem finiteL2Norm_sq [NormedSpace ℝ E] (μ : FiniteLaw Ω) (f : Ω → E) :
    finiteL2Norm μ f ^ (2 : ℕ) = μ.expect (fun ω => ‖f ω‖ ^ (2 : ℕ)) :=
  Real.sq_sqrt (μ.expect_nonneg fun _ω => sq_nonneg _)

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteDyadicMartingale
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {E : Type*} [NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]

theorem dyadicInputWeight_nonneg {N : ℕ} (a : DyadicAtom N) :
    0 ≤ dyadicInputWeight a := by
  cases a with
  | inl u => exact zero_le_one
  | inr a => exact (dyadicLaw a.1.val).mass_nonneg a.2

theorem dyadicIncrement_norm_predictable {N : ℕ} (φ : DyadicAtom N → E) (j : Fin N) :
    (dyadicFiltration N).AdaptedAt j.val (fun ω => ‖dyadicIncrement φ j ω‖) := by
  intro ω η h
  change ‖dyadicIncrement φ j ω‖ = ‖dyadicIncrement φ j η‖
  rw [norm_dyadicIncrement, norm_dyadicIncrement,
    dyadicPrefix_eq_of_rel (Nat.le_of_lt j.is_lt) h]

theorem dyadicIncrement_adapted {N : ℕ} (φ : DyadicAtom N → E) (j : Fin N) :
    (dyadicFiltration N).AdaptedAt (j.val + 1) (dyadicIncrement φ j) := by
  intro ω η h
  have hprefix := dyadicPrefix_eq_of_rel (Nat.le_of_lt j.is_lt)
    ((dyadicFiltration N).refines (Nat.le_succ j.val) h)
  have hbit : ω j = η j := h j (Nat.lt_succ_self j.val)
  simp only [dyadicIncrement, hprefix, hbit]

@[simp] theorem dyadicIncrement_flip {N : ℕ} (φ : DyadicAtom N → E)
    (j : Fin N) (ω : DyadicWord N) :
    dyadicIncrement φ j (dyadicFlip j ω) = -dyadicIncrement φ j ω := by
  simp only [dyadicIncrement, dyadicFlip_at, dyadicSign_not, dyadicFlip_prefix, neg_smul]

theorem dyadicIncrement_zero_conditional {N : ℕ} (φ : DyadicAtom N → E) (j : Fin N) :
    HasZeroConditionalSum (dyadicLaw N) ((dyadicFiltration N).part j.val)
      (dyadicIncrement φ j) := by
  classical
  intro a
  let f : DyadicWord N → E := fun ω =>
    if ((dyadicFiltration N).part j.val).r ω a then
      (dyadicLaw N).mass ω • dyadicIncrement φ j ω else 0
  have hflip (ω : DyadicWord N) : f (dyadicFlip j ω) = -f ω := by
    have hrel := dyadicFlip_rel j ω
    have hevent : ((dyadicFiltration N).part j.val).r (dyadicFlip j ω) a ↔
        ((dyadicFiltration N).part j.val).r ω a :=
      ⟨fun h => ((dyadicFiltration N).part j.val).trans'
          (((dyadicFiltration N).part j.val).symm' hrel) h,
        fun h => ((dyadicFiltration N).part j.val).trans' hrel h⟩
    simp only [f, hevent, dyadicLaw_mass, dyadicIncrement_flip, smul_neg]
    split_ifs <;> simp
  have hsum : (∑ ω, f ω) = -(∑ ω, f ω) := by
    calc
      _ = ∑ ω, f (dyadicFlip j ω) := ((dyadicFlipEquiv j).sum_comp f).symm
      _ = ∑ ω, -f ω := Finset.sum_congr rfl (fun ω _ => hflip ω)
      _ = -(∑ ω, f ω) := by rw [Finset.sum_neg_distrib]
  have hadd : (∑ ω, f ω) + (∑ ω, f ω) = 0 := add_eq_zero_iff_eq_neg.mpr hsum
  change (∑ ω, f ω) = 0
  calc
    _ = (2 : ℝ)⁻¹ • ((∑ ω, f ω) + (∑ ω, f ω)) := by module
    _ = 0 := by rw [hadd, smul_zero]

theorem dyadicProcess_difference_succ {N : ℕ} (φ : DyadicAtom N → E)
    (n : ℕ) (ω : DyadicWord N) :
    finiteDifference (dyadicProcess φ) (n + 1) ω =
      if hn : n < N then dyadicIncrement φ ⟨n, hn⟩ ω else 0 := by
  rw [finiteDifference_succ]
  simp only [dyadicProcess, add_sub_cancel_left]

theorem dyadicProcess_adapted {N : ℕ} (φ : DyadicAtom N → E) (n : ℕ) :
    (dyadicFiltration N).AdaptedAt n (dyadicProcess φ n) := by
  induction n with
  | zero => intro ω η h; rfl
  | succ n ih =>
      intro ω η h
      have hprev := ih ((dyadicFiltration N).refines (Nat.le_succ n) h)
      by_cases hn : n < N
      · have hinc := dyadicIncrement_adapted φ (⟨n, hn⟩ : Fin N) h
        simp only [dyadicProcess, dite_eq_left hn, hprev, hinc]
      · simp only [dyadicProcess, dite_eq_right hn, hprev]

theorem dyadicProcess_isMartingale {N : ℕ} (φ : DyadicAtom N → E) (K : ℕ) :
    (dyadicFiltration N).IsMartingaleUpTo (dyadicLaw N) (dyadicProcess φ) K := by
  refine ⟨fun n _ => dyadicProcess_adapted φ n, ?_⟩
  intro n hn hnK
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ n =>
      by_cases hnN : n < N
      · have hd : finiteDifference (dyadicProcess φ) (n + 1) =
            dyadicIncrement φ (⟨n, hnN⟩ : Fin N) := by
          funext ω
          rw [dyadicProcess_difference_succ, dite_eq_left hnN]
        simpa only [Nat.add_sub_cancel, hd] using
          dyadicIncrement_zero_conditional φ (⟨n, hnN⟩ : Fin N)
      · have hd : finiteDifference (dyadicProcess φ) (n + 1) = fun _ => (0 : E) := by
          funext ω
          rw [dyadicProcess_difference_succ, dite_eq_right hnN]
        simpa only [Nat.add_sub_cancel, hd] using
          hasZeroConditionalSum_zero (dyadicLaw N) ((dyadicFiltration N).part n)

theorem dyadicIncrement_moment {N : ℕ} (φ : DyadicAtom N → E) (p : ℝ) (j : Fin N) :
    finiteMoment (dyadicLaw N).mass p (dyadicIncrement φ j) =
      (dyadicLaw j.val).expect (fun α => ‖dyadicCoefficient φ j α‖ ^ p) := by
  change (dyadicLaw N).expect (fun ω => ‖dyadicIncrement φ j ω‖ ^ p) = _
  simp_rw [norm_dyadicIncrement]
  exact dyadicLaw_expect_prefix (Nat.le_of_lt j.is_lt)
    (fun α => ‖dyadicCoefficient φ j α‖ ^ p)

omit sectionNormedSpaceℝE in
theorem dyadicInputMoment_prefixes [NormedSpace ℝ E] {N : ℕ} (φ : DyadicAtom N → E) (p : ℝ) :
    finiteMoment dyadicInputWeight p φ = ‖dyadicRoot φ‖ ^ p +
      ∑ j : Fin N, (dyadicLaw j.val).expect (fun α => ‖dyadicCoefficient φ j α‖ ^ p) := by
  classical
  simp only [finiteMoment, Fintype.sum_sum_type, Fintype.sum_sigma,
    dyadicInputWeight, dyadicRoot, dyadicCoefficient, FiniteLaw.expect]
  simp

theorem dyadicInputMoment {N : ℕ} (φ : DyadicAtom N → E) (p : ℝ) :
    finiteMoment dyadicInputWeight p φ = ‖dyadicRoot φ‖ ^ p +
      ∑ j : Fin N, finiteMoment (dyadicLaw N).mass p (dyadicIncrement φ j) := by
  simp_rw [dyadicIncrement_moment]
  exact dyadicInputMoment_prefixes φ p

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteSmoothMoments
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {X : Type*} [NormedAddCommGroup X] [sectionNormedSpaceℝX : NormedSpace ℝ X]
variable {q D : ℝ}

theorem norm_rpow_sum_smul_le {ι : Type*} (s : Finset ι)
    (p : ι → ℝ) (z : ι → X) (hp : ∀ i ∈ s, 0 ≤ p i)
    (hsum : ∑ i ∈ s, p i = 1) (hq : 1 ≤ q) :
    ‖∑ i ∈ s, p i • z i‖ ^ q ≤ ∑ i ∈ s, p i * ‖z i‖ ^ q := by
  have hn : ‖∑ i ∈ s, p i • z i‖ ≤ ∑ i ∈ s, p i * ‖z i‖ := by
    calc
      _ ≤ ∑ i ∈ s, ‖p i • z i‖ := norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [norm_smul, Real.norm_of_nonneg (hp i hi)]
  exact (Real.rpow_le_rpow (norm_nonneg _) hn (by linarith)).trans
    (Real.rpow_arith_mean_le_arith_mean_rpow s p (fun i => ‖z i‖)
      hp hsum (fun i _ => norm_nonneg _) hq)

theorem finite_norm_rpow_jensen {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (z : ι → X) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (hq : 1 ≤ q) :
    ‖∑ i, p i • z i‖ ^ q ≤ ∑ i, p i * ‖z i‖ ^ q :=
  norm_rpow_sum_smul_le Finset.univ p z (fun i _ => hp i) hsum hq

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteConditionalAverage
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity.FiniteLaw

variable {Ω K J : Type*} [Fintype Ω] [DecidableEq K] [DecidableEq J]

theorem fiberWeight_nonneg (μ : FiniteLaw Ω) (key : Ω → K) (a : K) (ω : Ω) :
    0 ≤ μ.fiberWeight key a ω := by
  by_cases h : key ω = a
  · simpa [fiberWeight, h] using μ.mass_nonneg ω
  · simp [fiberWeight, h]

theorem fiberMass_nonneg (μ : FiniteLaw Ω) (key : Ω → K) (a : K) :
    0 ≤ μ.fiberMass key a :=
  Finset.sum_nonneg fun ω _ => μ.fiberWeight_nonneg key a ω

theorem mass_le_fiberMass (μ : FiniteLaw Ω) (key : Ω → K) (ω : Ω) :
    μ.mass ω ≤ μ.fiberMass key (key ω) := by
  have h := Finset.single_le_sum
    (fun ν (_ : ν ∈ (Finset.univ : Finset Ω)) => μ.fiberWeight_nonneg key (key ω) ν)
    (Finset.mem_univ ω)
  have hself : μ.fiberWeight key (key ω) ω = μ.mass ω := ite_eq_left rfl
  rw [hself] at h
  exact h

theorem fiberMass_pos_of_mass_pos (μ : FiniteLaw Ω) (key : Ω → K) {ω : Ω}
    (hω : 0 < μ.mass ω) : 0 < μ.fiberMass key (key ω) :=
  hω.trans_le (μ.mass_le_fiberMass key ω)

theorem fiberWeight_eq_zero_of_fiberMass_eq_zero (μ : FiniteLaw Ω)
    (key : Ω → K) (a : K) (hzero : μ.fiberMass key a = 0) (ω : Ω) :
    μ.fiberWeight key a ω = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg
    (fun ν (_ : ν ∈ (Finset.univ : Finset Ω)) => μ.fiberWeight_nonneg key a ν)).mp
    hzero ω (Finset.mem_univ ω)

theorem normalizedFiberWeight_nonneg (μ : FiniteLaw Ω) (key : Ω → K)
    (a : K) (ω : Ω) : 0 ≤ μ.normalizedFiberWeight key a ω :=
  mul_nonneg (inv_nonneg.mpr (μ.fiberMass_nonneg key a))
    (μ.fiberWeight_nonneg key a ω)

theorem sum_normalizedFiberWeight (μ : FiniteLaw Ω) (key : Ω → K) (a : K)
    (hpos : 0 < μ.fiberMass key a) :
    ∑ ω, μ.normalizedFiberWeight key a ω = 1 := by
  simp only [normalizedFiberWeight, ← Finset.mul_sum]
  change (μ.fiberMass key a)⁻¹ * μ.fiberMass key a = 1
  exact inv_mul_cancel₀ hpos.ne'

section Module

variable {E : Type*} [AddCommMonoid E] [Module ℝ E]

theorem fiberSum_eq_zero_of_fiberMass_eq_zero (μ : FiniteLaw Ω)
    (key : Ω → K) (F : Ω → E) (a : K) (hzero : μ.fiberMass key a = 0) :
    μ.fiberSum key F a = 0 := by
  apply Finset.sum_eq_zero
  intro ω _
  rw [μ.fiberWeight_eq_zero_of_fiberMass_eq_zero key a hzero ω, zero_smul]

theorem conditionalMean_eq_sum_normalizedFiberWeight (μ : FiniteLaw Ω)
    (key : Ω → K) (F : Ω → E) (a : K) :
    μ.conditionalMean key F a = ∑ ω, μ.normalizedFiberWeight key a ω • F ω := by
  simp only [conditionalMean, fiberSum, normalizedFiberWeight, Finset.smul_sum, smul_smul]

theorem mass_smul_conditionalMean (μ : FiniteLaw Ω) (key : Ω → K)
    (F : Ω → E) (a : K) :
    μ.fiberMass key a • μ.conditionalMean key F a = μ.fiberSum key F a := by
  by_cases hzero : μ.fiberMass key a = 0
  · rw [hzero, zero_smul, μ.fiberSum_eq_zero_of_fiberMass_eq_zero key F a hzero]
  · simp only [conditionalMean, smul_smul, mul_inv_cancel₀ hzero, one_smul]

theorem conditionalAverage_eq_of_key_eq (μ : FiniteLaw Ω) (key : Ω → K)
    (F : Ω → E) {ω ν : Ω} (h : key ω = key ν) :
    μ.conditionalAverage key F ω = μ.conditionalAverage key F ν := by
  simp only [conditionalAverage, h]

theorem fiberSum_key (μ : FiniteLaw Ω) (key : Ω → K) (G : K → E) (a : K) :
    μ.fiberSum key (fun ω => G (key ω)) a = μ.fiberMass key a • G a := by
  simp only [fiberSum, fiberMass, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : key ω = a <;> simp [fiberWeight, h]

theorem conditionalMean_key (μ : FiniteLaw Ω) (key : Ω → K) (G : K → E)
    (a : K) (hpos : 0 < μ.fiberMass key a) :
    μ.conditionalMean key (fun ω => G (key ω)) a = G a := by
  rw [conditionalMean, μ.fiberSum_key, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]

theorem conditionalAverage_key_of_mass_pos (μ : FiniteLaw Ω) (key : Ω → K)
    (G : K → E) (ω : Ω) (hpos : 0 < μ.mass ω) :
    μ.conditionalAverage key (fun ν => G (key ν)) ω = G (key ω) :=
  μ.conditionalMean_key key G (key ω) (μ.fiberMass_pos_of_mass_pos key hpos)

theorem mass_smul_conditionalAverage_key (μ : FiniteLaw Ω) (key : Ω → K)
    (G : K → E) (ω : Ω) :
    μ.mass ω • μ.conditionalAverage key (fun ν => G (key ν)) ω =
      μ.mass ω • G (key ω) := by
  by_cases hzero : μ.mass ω = 0
  · simp only [hzero, zero_smul]
  · have hpos : 0 < μ.mass ω := lt_of_le_of_ne (μ.mass_nonneg ω) (Ne.symm hzero)
    rw [μ.conditionalAverage_key_of_mass_pos key G ω hpos]

theorem fiberSum_eq_vexpect_indicator (μ : FiniteLaw Ω) (key : Ω → K)
    (F : Ω → E) (a : K) :
    μ.fiberSum key F a = μ.vexpect (fun ω => if key ω = a then F ω else 0) := by
  simp only [fiberSum, vexpect]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : key ω = a <;> simp [fiberWeight, h]

variable [Fintype K]

theorem sum_fiberSum (μ : FiniteLaw Ω) (key : Ω → K) (F : Ω → E) :
    ∑ a, μ.fiberSum key F a = μ.vexpect F := by
  simp only [fiberSum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp [fiberWeight, ite_smul]

theorem vexpect_key (μ : FiniteLaw Ω) (key : Ω → K) (G : K → E) :
    μ.vexpect (fun ω => G (key ω)) = ∑ a, μ.fiberMass key a • G a := by
  symm
  simp only [fiberMass, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp [fiberWeight, ite_smul]

theorem vexpect_key_smul (μ : FiniteLaw Ω) (key : Ω → K)
    (F : Ω → E) (c : K → ℝ) :
    μ.vexpect (fun ω => c (key ω) • F ω) = ∑ a, c a • μ.fiberSum key F a := by
  symm
  simp only [fiberSum, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp [fiberWeight, smul_smul, mul_comm, ite_smul]

theorem vexpect_key_smul_eq_zero (μ : FiniteLaw Ω) (key : Ω → K)
    (F : Ω → E) (hzero : ∀ a, μ.fiberSum key F a = 0) (c : K → ℝ) :
    μ.vexpect (fun ω => c (key ω) • F ω) = 0 := by
  rw [μ.vexpect_key_smul key F c]
  simp only [hzero, smul_zero, Finset.sum_const_zero]

theorem vexpect_key_indicator_eq_zero (μ : FiniteLaw Ω) (key : Ω → K)
    (F : Ω → E) (hzero : ∀ a, μ.fiberSum key F a = 0)
    (P : K → Prop) [DecidablePred P] :
    μ.vexpect (fun ω => if P (key ω) then F ω else 0) = 0 := by
  simpa only [ite_smul, one_smul, zero_smul] using
    μ.vexpect_key_smul_eq_zero key F hzero (fun a => if P a then 1 else 0)

theorem vexpect_conditionalAverage (μ : FiniteLaw Ω) (key : Ω → K) (F : Ω → E) :
    μ.vexpect (μ.conditionalAverage key F) = μ.vexpect F := by
  change μ.vexpect (fun ω => μ.conditionalMean key F (key ω)) = _
  rw [μ.vexpect_key]
  simp only [μ.mass_smul_conditionalMean]
  exact μ.sum_fiberSum key F

theorem vexpect_key_smul_conditionalAverage (μ : FiniteLaw Ω) (key : Ω → K)
    (F : Ω → E) (c : K → ℝ) :
    μ.vexpect (fun ω => c (key ω) • μ.conditionalAverage key F ω) =
      μ.vexpect (fun ω => c (key ω) • F ω) := by
  change μ.vexpect (fun ω => (fun a => c a • μ.conditionalMean key F a) (key ω)) = _
  rw [μ.vexpect_key key (fun a => c a • μ.conditionalMean key F a),
    μ.vexpect_key_smul key F c]
  apply Finset.sum_congr rfl
  intro a _
  rw [smul_smul, mul_comm (μ.fiberMass key a) (c a), ← smul_smul,
    μ.mass_smul_conditionalMean]

theorem fiberSum_conditionalAverage_comp (μ : FiniteLaw Ω) (key : Ω → K)
    (parent : K → J) (F : Ω → E) (a : J) :
    μ.fiberSum (parent ∘ key) (μ.conditionalAverage key F) a =
      μ.fiberSum (parent ∘ key) F a := by
  rw [μ.fiberSum_eq_vexpect_indicator, μ.fiberSum_eq_vexpect_indicator]
  simpa only [Function.comp_apply, ite_smul, one_smul, zero_smul] using
    μ.vexpect_key_smul_conditionalAverage key F
      (fun b => if parent b = a then 1 else 0)

end Module

theorem expect_conditionalAverage [Fintype K] (μ : FiniteLaw Ω)
    (key : Ω → K) (F : Ω → ℝ) :
    μ.expect (μ.conditionalAverage key F) = μ.expect F := by
  simpa only [expect, vexpect, smul_eq_mul] using μ.vexpect_conditionalAverage key F

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem conditionalMean_norm_rpow_le (μ : FiniteLaw Ω) (key : Ω → K)
    (F : Ω → E) {q : ℝ} (hq : 1 ≤ q) (a : K) :
    ‖μ.conditionalMean key F a‖ ^ q ≤
      μ.conditionalMean key (fun ω => ‖F ω‖ ^ q) a := by
  by_cases hzero : μ.fiberMass key a = 0
  · have hqne : q ≠ 0 := by linarith
    simp [conditionalMean, hzero, Real.zero_rpow hqne]
  · have hpos : 0 < μ.fiberMass key a :=
      lt_of_le_of_ne (μ.fiberMass_nonneg key a) (Ne.symm hzero)
    have hj := finite_norm_rpow_jensen (μ.normalizedFiberWeight key a) F
      (μ.normalizedFiberWeight_nonneg key a) (μ.sum_normalizedFiberWeight key a hpos) hq
    rw [← μ.conditionalMean_eq_sum_normalizedFiberWeight key F a] at hj
    simpa only [conditionalMean, fiberSum, normalizedFiberWeight, smul_eq_mul,
      Finset.mul_sum, mul_assoc] using hj

theorem conditionalAverage_norm_rpow_le (μ : FiniteLaw Ω) (key : Ω → K)
    (F : Ω → E) {q : ℝ} (hq : 1 ≤ q) (ω : Ω) :
    ‖μ.conditionalAverage key F ω‖ ^ q ≤
      μ.conditionalAverage key (fun ν => ‖F ν‖ ^ q) ω :=
  μ.conditionalMean_norm_rpow_le key F hq (key ω)

theorem expect_norm_conditionalAverage_rpow_le [Fintype K] (μ : FiniteLaw Ω)
    (key : Ω → K) (F : Ω → E) {q : ℝ} (hq : 1 ≤ q) :
    μ.expect (fun ω => ‖μ.conditionalAverage key F ω‖ ^ q) ≤
      μ.expect (fun ω => ‖F ω‖ ^ q) := by
  calc
    _ ≤ μ.expect (μ.conditionalAverage key (fun ω => ‖F ω‖ ^ q)) :=
      μ.expect_mono (μ.conditionalAverage_norm_rpow_le key F hq)
    _ = _ := μ.expect_conditionalAverage key (fun ω => ‖F ω‖ ^ q)

end MarkovSuperreflexivity.FiniteLaw

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteMartingaleConditional
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

variable {Ω E : Type*} [sectionFintypeΩ : Fintype Ω]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem HasZeroConditionalSum.sum_indicator {μ : FiniteLaw Ω} {P : Setoid Ω}
    {f : Ω → E} (hf : HasZeroConditionalSum μ P f) (A : Ω → Prop)
    (hA : ∀ {ω η}, P.r ω η → (A ω ↔ A η)) :
    (∑ ω, if A ω then μ.mass ω • f ω else 0) = 0 := by
  classical
  let key : Ω → Quotient P := Quotient.mk P
  let B : Quotient P → Prop := Quotient.lift A (fun _ _ h => propext (hA h))
  have hzero (a : Quotient P) : μ.fiberSum key f a = 0 := by
    refine Quotient.inductionOn a ?_
    intro a
    simpa only [FiniteLaw.fiberSum, FiniteLaw.fiberWeight, key,
      Quotient.eq, ite_smul, zero_smul] using hf a
  have h := μ.vexpect_key_indicator_eq_zero key f hzero B
  change (∑ ω, μ.mass ω • (if A ω then f ω else 0)) = 0 at h
  simpa only [smul_ite, smul_zero] using h

theorem HasZeroConditionalSum.of_refinement {μ : FiniteLaw Ω}
    {P Q : Setoid Ω} {f : Ω → E} (hf : HasZeroConditionalSum μ Q f)
    (hPQ : ∀ {ω η}, Q.r ω η → P.r ω η) : HasZeroConditionalSum μ P f := by
  intro a
  apply hf.sum_indicator (fun ω => P.r ω a)
  intro ω η hωη
  have hp := hPQ hωη
  exact ⟨fun h => P.trans' (P.symm' hp) h, fun h => P.trans' hp h⟩

namespace FinitePartitionFiltration

variable {F : FinitePartitionFiltration Ω} {μ : FiniteLaw Ω}
variable {M : ℕ → Ω → E} {N : ℕ}

theorem IsMartingaleUpTo.terminal_atom_sum (hM : F.IsMartingaleUpTo μ M N)
    {j : ℕ} (hj : j ≤ N) (a : Ω) :
    (∑ ω, if (F.part j).r ω a then μ.mass ω • M N ω else 0) =
      ∑ ω, if (F.part j).r ω a then μ.mass ω • M j ω else 0 := by
  classical
  have haux : ∀ n : ℕ, j ≤ n → n ≤ N →
      (∑ ω, if (F.part j).r ω a then μ.mass ω • M n ω else 0) =
        ∑ ω, if (F.part j).r ω a then μ.mass ω • M j ω else 0 := by
    intro n
    induction n with
    | zero =>
      intro hjn hnN
      have hj0 : j = 0 := Nat.eq_zero_of_le_zero hjn
      subst j
      rfl
    | succ n ih =>
      intro hjn hnN
      by_cases heq : j = n + 1
      · subst j
        rfl
      · have hjn' : j ≤ n := by omega
        have hnn : n ≤ N := (Nat.le_succ n).trans hnN
        have hz : HasZeroConditionalSum μ (F.part n)
            (finiteDifference M (n + 1)) := by
          simpa only [Nat.add_sub_cancel] using hM.2 (n + 1) (Nat.succ_pos n) hnN
        have hz' : HasZeroConditionalSum μ (F.part j)
            (finiteDifference M (n + 1)) :=
          hz.of_refinement (fun {_ _} h => F.refines hjn' h)
        have hstep := hz' a
        have hdiff :
            (∑ ω, if (F.part j).r ω a then μ.mass ω • M (n + 1) ω else 0) -
              (∑ ω, if (F.part j).r ω a then μ.mass ω • M n ω else 0) = 0 := by
          calc
            _ = ∑ ω, if (F.part j).r ω a then
                μ.mass ω • (M (n + 1) ω - M n ω) else 0 := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro ω _
              by_cases h : (F.part j).r ω a <;> simp only [h, ite_true, ite_false,
                smul_sub, sub_zero]
            _ = 0 := by simpa only [finiteDifference_succ] using hstep
        exact (sub_eq_zero.mp hdiff).trans (ih hjn' hnn)
  exact haux N hj le_rfl

omit sectionFintypeΩ in
theorem stopped_rel_iff_at_time [Fintype Ω] {τ : Ω → ℕ} (hτ : F.IsStoppingTime τ)
    (ω a : Ω) : (F.stoppedSetoid τ).r ω a ↔ (F.part (τ a)).r ω a := by
  constructor
  · intro h
    rw [← h.1]
    exact h.2
  · intro h
    exact (F.stoppedSetoid τ).symm'
      (F.stopped_rel_of_rel_of_le hτ ((F.part (τ a)).symm' h) le_rfl)

theorem IsMartingaleUpTo.stopped_atom_sum (hM : F.IsMartingaleUpTo μ M N)
    {τ : Ω → ℕ} (hτ : F.IsStoppingTime τ) (hτN : ∀ ω, τ ω ≤ N) (a : Ω) :
    (∑ ω, if (F.stoppedSetoid τ).r ω a then μ.mass ω • M N ω else 0) =
      (∑ ω, if (F.stoppedSetoid τ).r ω a then μ.mass ω else 0) • M (τ a) a := by
  classical
  simp only [stopped_rel_iff_at_time hτ]
  rw [hM.terminal_atom_sum (hτN a) a, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : (F.part (τ a)).r ω a
  · simp only [ite_eq_left h, hM.1 (τ a) (hτN a) h]
  · simp only [ite_eq_right h, zero_smul]

theorem IsMartingaleUpTo.conditional_terminal_stopped_of_mass_pos
    (hM : F.IsMartingaleUpTo μ M N) {τ : Ω → ℕ}
    (hτ : F.IsStoppingTime τ) (hτN : ∀ ω, τ ω ≤ N)
    (ω : Ω) (hω : 0 < μ.mass ω) :
    μ.conditionalAverage (Quotient.mk (F.stoppedSetoid τ)) (M N) ω = M (τ ω) ω := by
  classical
  let key := Quotient.mk (F.stoppedSetoid τ)
  have hmass : 0 < μ.fiberMass key (key ω) := μ.fiberMass_pos_of_mass_pos key hω
  have hsum : μ.fiberSum key (M N) (key ω) =
      μ.fiberMass key (key ω) • M (τ ω) ω := by
    simpa only [FiniteLaw.fiberSum, FiniteLaw.fiberMass, FiniteLaw.fiberWeight,
      key, Quotient.eq, ite_smul, zero_smul] using hM.stopped_atom_sum hτ hτN ω
  change (μ.fiberMass key (key ω))⁻¹ • μ.fiberSum key (M N) (key ω) = _
  rw [hsum, smul_smul, inv_mul_cancel₀ hmass.ne', one_smul]

theorem IsMartingaleUpTo.conditional_terminal_of_mass_pos
    (hM : F.IsMartingaleUpTo μ M N) {j : ℕ} (hj : j ≤ N)
    (ω : Ω) (hω : 0 < μ.mass ω) :
    μ.conditionalAverage (Quotient.mk (F.part j)) (M N) ω = M j ω := by
  classical
  let key := Quotient.mk (F.part j)
  have hmass : 0 < μ.fiberMass key (key ω) := μ.fiberMass_pos_of_mass_pos key hω
  have hsum : μ.fiberSum key (M N) (key ω) =
      μ.fiberMass key (key ω) • M j ω := by
    simp only [FiniteLaw.fiberSum, FiniteLaw.fiberMass, FiniteLaw.fiberWeight,
      key, Quotient.eq, ite_smul, zero_smul]
    rw [hM.terminal_atom_sum hj ω, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro η _
    by_cases h : (F.part j).r η ω
    · simp only [ite_eq_left h, hM.1 j hj h]
    · simp only [ite_eq_right h, zero_smul]
  change (μ.fiberMass key (key ω))⁻¹ • μ.fiberSum key (M N) (key ω) = _
  rw [hsum, smul_smul, inv_mul_cancel₀ hmass.ne', one_smul]

theorem IsMartingaleUpTo.expect_stopped_norm_sq_le
    (hM : F.IsMartingaleUpTo μ M N) {τ : Ω → ℕ}
    (hτ : F.IsStoppingTime τ) (hτN : ∀ ω, τ ω ≤ N) :
    μ.expect (fun ω => ‖M (τ ω) ω‖ ^ (2 : ℕ)) ≤
      μ.expect (fun ω => ‖M N ω‖ ^ (2 : ℕ)) := by
  classical
  let key := Quotient.mk (F.stoppedSetoid τ)
  calc
    μ.expect (fun ω => ‖M (τ ω) ω‖ ^ (2 : ℕ)) =
        μ.expect (fun ω => ‖μ.conditionalAverage key (M N) ω‖ ^ (2 : ℕ)) := by
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hzero : μ.mass ω = 0
      · simp only [hzero, zero_mul]
      · have hpos := lt_of_le_of_ne (μ.mass_nonneg ω) (Ne.symm hzero)
        change μ.mass ω * ‖M (τ ω) ω‖ ^ (2 : ℕ) =
          μ.mass ω * ‖μ.conditionalAverage (Quotient.mk (F.stoppedSetoid τ)) (M N) ω‖ ^ (2 : ℕ)
        rw [hM.conditional_terminal_stopped_of_mass_pos hτ hτN ω hpos]
    _ ≤ _ := by
      simpa only [Real.rpow_two] using
        μ.expect_norm_conditionalAverage_rpow_le key (M N) (q := (2 : ℝ)) (by norm_num)

end FinitePartitionFiltration

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteConditionalMartingale
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity
namespace FinitePartitionFiltration

variable {Ω : Type*} (F : FinitePartitionFiltration Ω)

theorem quotientCoarsening_comp {i j : ℕ} (hij : i ≤ j) :
    F.quotientCoarsening hij ∘ Quotient.mk (F.part j) =
      Quotient.mk (F.part i) := rfl

variable [Fintype Ω] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem adaptedAt_conditionalProcess (μ : FiniteLaw Ω) (f : Ω → E) (j : ℕ) :
    F.AdaptedAt j (F.conditionalProcess μ f j) := by
  intro ω η hωη
  exact μ.conditionalAverage_eq_of_key_eq (Quotient.mk (F.part j)) f
    (Quotient.sound hωη)

theorem fiberSum_conditionalProcess (μ : FiniteLaw Ω) (f : Ω → E)
    {i j : ℕ} (hij : i ≤ j) (a : Quotient (F.part i)) :
    μ.fiberSum (Quotient.mk (F.part i)) (F.conditionalProcess μ f j) a =
      μ.fiberSum (Quotient.mk (F.part i)) f a := by
  have h := μ.fiberSum_conditionalAverage_comp (Quotient.mk (F.part j))
    (F.quotientCoarsening hij) f a
  rw [F.quotientCoarsening_comp hij] at h
  exact h

theorem atom_sum_conditionalProcess (μ : FiniteLaw Ω) (f : Ω → E)
    {i j : ℕ} (hij : i ≤ j) (a : Ω) :
    (∑ ω, if (F.part i).r ω a then
      μ.mass ω • F.conditionalProcess μ f j ω else 0) =
      ∑ ω, if (F.part i).r ω a then μ.mass ω • f ω else 0 := by
  simpa only [FiniteLaw.fiberSum, FiniteLaw.fiberWeight, Quotient.eq,
    ite_smul, zero_smul] using
    F.fiberSum_conditionalProcess μ f hij (Quotient.mk (F.part i) a)

theorem hasZeroConditionalSum_conditionalProcess_sub (μ : FiniteLaw Ω) (f : Ω → E)
    {i j : ℕ} (hij : i ≤ j) :
    HasZeroConditionalSum μ (F.part i)
      (fun ω => F.conditionalProcess μ f j ω - F.conditionalProcess μ f i ω) := by
  intro a
  calc
    _ = (∑ ω, if (F.part i).r ω a then
        μ.mass ω • F.conditionalProcess μ f j ω else 0) -
        ∑ ω, if (F.part i).r ω a then
          μ.mass ω • F.conditionalProcess μ f i ω else 0 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro ω _
      by_cases h : (F.part i).r ω a <;>
        simp only [h, ite_true, ite_false, smul_sub, sub_zero]
    _ = 0 := by
      rw [F.atom_sum_conditionalProcess μ f hij,
        F.atom_sum_conditionalProcess μ f (i := i) le_rfl, sub_self]

theorem isMartingaleUpTo_conditionalProcess (μ : FiniteLaw Ω) (f : Ω → E) (N : ℕ) :
    F.IsMartingaleUpTo μ (F.conditionalProcess μ f) N := by
  constructor
  · intro j _
    exact F.adaptedAt_conditionalProcess μ f j
  · intro j hj _
    simpa only [finiteDifference, ite_eq_right (Nat.ne_of_gt hj)] using
      F.hasZeroConditionalSum_conditionalProcess_sub μ f (Nat.sub_le j 1)

theorem finiteL2Norm_conditionalProcess_le (μ : FiniteLaw Ω) (f : Ω → E) (j : ℕ) :
    finiteL2Norm μ (F.conditionalProcess μ f j) ≤ finiteL2Norm μ f := by
  apply Real.sqrt_le_sqrt
  simpa only [conditionalProcess, Real.rpow_two] using
    μ.expect_norm_conditionalAverage_rpow_le (Quotient.mk (F.part j)) f
      (q := (2 : ℝ)) (by norm_num)

end FinitePartitionFiltration
end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteMartingalePairing
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {Ω E : Type*} [Fintype Ω]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace FiniteLaw

variable {K : Type*} [Fintype K] [DecidableEq K]

theorem expect_pair_key_right_clm (μ : FiniteLaw Ω) (key : Ω → K)
    (G : Ω → E →L[ℝ] ℝ) (H : K → E) :
    μ.expect (fun ω => G ω (H (key ω))) = ∑ a, (μ.fiberSum key G a) (H a) := by
  symm
  simp only [fiberSum, sum_apply,
    smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp [fiberWeight, ite_mul]

theorem expect_pair_key_left_clm (μ : FiniteLaw Ω) (key : Ω → K)
    (H : K → E →L[ℝ] ℝ) (f : Ω → E) :
    μ.expect (fun ω => H (key ω) (f ω)) = ∑ a, H a (μ.fiberSum key f a) := by
  symm
  simp only [fiberSum, map_sum, map_smul, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp [fiberWeight, ite_mul]

theorem expect_pair_conditionalAverage_clm (μ : FiniteLaw Ω) (key : Ω → K)
    (f : Ω → E) (G : Ω → E →L[ℝ] ℝ) :
    μ.expect (fun ω => G ω (μ.conditionalAverage key f ω)) =
      μ.expect (fun ω => (μ.conditionalAverage key G ω) (f ω)) := by
  change μ.expect (fun ω => G ω (μ.conditionalMean key f (key ω))) =
    μ.expect (fun ω => (μ.conditionalMean key G (key ω)) (f ω))
  rw [μ.expect_pair_key_right_clm, μ.expect_pair_key_left_clm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [conditionalMean, map_smul, smul_apply]

end FiniteLaw

namespace FinitePartitionFiltration

theorem expect_pair_conditionalProcess_of_adapted (F : FinitePartitionFiltration Ω)
    (μ : FiniteLaw Ω) (f : Ω → E) (j : ℕ) {G : Ω → E →L[ℝ] ℝ}
    (hG : F.AdaptedAt j G) :
    μ.expect (fun ω => G ω (F.conditionalProcess μ f j ω)) =
      μ.expect (fun ω => G ω (f ω)) := by
  classical
  rw [conditionalProcess, μ.expect_pair_conditionalAverage_clm]
  let key : Ω → Quotient (F.part j) := Quotient.mk (F.part j)
  let H : Quotient (F.part j) → E →L[ℝ] ℝ :=
    Quotient.lift G (fun _ _ h => hG h)
  unfold FiniteLaw.expect
  apply Finset.sum_congr rfl
  intro ω _
  have h := μ.mass_smul_conditionalAverage_key key H ω
  change μ.mass ω • μ.conditionalAverage (Quotient.mk (F.part j)) G ω =
    μ.mass ω • G ω at h
  have he := congrArg (fun L : E →L[ℝ] ℝ => L (f ω)) h
  simpa only [smul_apply, smul_eq_mul] using he

end FinitePartitionFiltration

theorem HasZeroConditionalSum.expect_pair_of_atom_constant
    {μ : FiniteLaw Ω} {P : Setoid Ω} {G : Ω → E →L[ℝ] ℝ}
    (hG : HasZeroConditionalSum μ P G) (z : Ω → E)
    (hz : ∀ {ω η}, P.r ω η → z ω = z η) :
    μ.expect (fun ω => G ω (z ω)) = 0 := by
  classical
  let key : Ω → Quotient P := Quotient.mk P
  let H : Quotient P → E := Quotient.lift z (fun _ _ h => hz h)
  change μ.expect (fun ω => G ω (H (key ω))) = 0
  rw [μ.expect_pair_key_right_clm]
  apply Finset.sum_eq_zero
  intro a _
  have hsum : μ.fiberSum key G a = 0 := by
    refine Quotient.inductionOn a ?_
    intro ω
    simpa only [FiniteLaw.fiberSum, FiniteLaw.fiberWeight, key,
      Quotient.eq, ite_smul, zero_smul] using hG ω
  simp only [hsum, zero_apply]

theorem sum_finiteDifference_eq (M : ℕ → Ω → E) (N : ℕ) (ω : Ω) :
    (∑ j ∈ Finset.range (N + 1), finiteDifference M j ω) = M N ω := by
  induction N with
  | zero =>
      change (∑ j ∈ Finset.range 1, finiteDifference M j ω) = M 0 ω
      exact (Finset.sum_range_one _).trans (congrFun (finiteDifference_zero M) ω)
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, finiteDifference_succ]
      abel

theorem finite_martingale_difference_pairing
    {F : FinitePartitionFiltration Ω} {μ : FiniteLaw Ω}
    {G : ℕ → Ω → E →L[ℝ] ℝ} {N j : ℕ}
    (hG : F.IsMartingaleUpTo μ G N) (f : Ω → E) (hj : j ≤ N) :
    μ.expect (fun ω => finiteDifference G j ω (f ω)) =
      μ.expect (fun ω => finiteDifference G j ω
        (finiteDifference (F.conditionalProcess μ f) j ω)) := by
  have ha := F.expect_pair_conditionalProcess_of_adapted μ f j
    (hG.difference_adapted hj)
  cases j with
  | zero =>
      simpa only [finiteDifference_zero] using ha.symm
  | succ k =>
      have hz : HasZeroConditionalSum μ (F.part k) (finiteDifference G (k + 1)) := by
        simpa only [Nat.add_sub_cancel] using hG.2 (k + 1) (Nat.succ_pos k) hj
      have hzero := hz.expect_pair_of_atom_constant
        (F.conditionalProcess μ f k) (F.adaptedAt_conditionalProcess μ f k)
      have hsub :
          μ.expect (fun ω => finiteDifference G (k + 1) ω
            (F.conditionalProcess μ f (k + 1) ω - F.conditionalProcess μ f k ω)) =
          μ.expect (fun ω => finiteDifference G (k + 1) ω
            (F.conditionalProcess μ f (k + 1) ω)) -
          μ.expect (fun ω => finiteDifference G (k + 1) ω
            (F.conditionalProcess μ f k ω)) := by
        simp only [map_sub, FiniteLaw.expect, mul_sub, Finset.sum_sub_distrib]
      rw [hzero, sub_zero] at hsub
      simpa only [finiteDifference_succ] using ha.symm.trans hsub.symm

theorem finite_martingale_terminal_pairing
    {F : FinitePartitionFiltration Ω} {μ : FiniteLaw Ω}
    {G : ℕ → Ω → E →L[ℝ] ℝ} {N : ℕ}
    (hG : F.IsMartingaleUpTo μ G N) (f : Ω → E) :
    μ.expect (fun ω => G N ω (f ω)) =
      ∑ j ∈ Finset.range (N + 1), μ.expect (fun ω =>
        finiteDifference G j ω (finiteDifference (F.conditionalProcess μ f) j ω)) := by
  calc
    μ.expect (fun ω => G N ω (f ω)) =
        μ.expect (fun ω => (∑ j ∈ Finset.range (N + 1),
          finiteDifference G j ω) (f ω)) := by
      congr 1
      funext ω
      rw [sum_finiteDifference_eq]
    _ = ∑ j ∈ Finset.range (N + 1),
        μ.expect (fun ω => finiteDifference G j ω (f ω)) := by
      simp only [FiniteLaw.expect, sum_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact finite_martingale_difference_pairing hG f (Nat.lt_succ_iff.mp
        (Finset.mem_range.mp hj))

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_DyadicSynthesisPairing
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finite_martingale_terminal_pairing_of_martingales
    {Ω : Type*} [Fintype Ω] {F : FinitePartitionFiltration Ω} {μ : FiniteLaw Ω}
    {G : ℕ → Ω → E →L[ℝ] ℝ} {M : ℕ → Ω → E} {N : ℕ}
    (hG : F.IsMartingaleUpTo μ G N) (hM : F.IsMartingaleUpTo μ M N) :
    μ.expect (fun ω => G N ω (M N ω)) =
      ∑ j ∈ Finset.range (N + 1),
        μ.expect (fun ω => finiteDifference G j ω (finiteDifference M j ω)) := by
  classical
  rw [finite_martingale_terminal_pairing hG (M N)]
  apply Finset.sum_congr rfl
  intro j hj
  have hjN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hdiff (ω : Ω) (hω : 0 < μ.mass ω) :
      finiteDifference (F.conditionalProcess μ (M N)) j ω = finiteDifference M j ω := by
    cases j with
    | zero =>
      simpa only [finiteDifference_zero, FinitePartitionFiltration.conditionalProcess] using
        hM.conditional_terminal_of_mass_pos hjN ω hω
    | succ j =>
      rw [finiteDifference_succ, finiteDifference_succ]
      change μ.conditionalAverage (Quotient.mk (F.part (j + 1))) (M N) ω -
        μ.conditionalAverage (Quotient.mk (F.part j)) (M N) ω = _
      rw [hM.conditional_terminal_of_mass_pos hjN ω hω,
        hM.conditional_terminal_of_mass_pos ((Nat.le_succ j).trans hjN) ω hω]
  unfold FiniteLaw.expect
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hz : μ.mass ω = 0
  · simp only [hz, zero_mul]
  · exact congrArg (fun x : E => μ.mass ω * finiteDifference G j ω x)
      (hdiff ω (lt_of_le_of_ne (μ.mass_nonneg ω) (Ne.symm hz)))

theorem dyadicIncrement_pairing {N : ℕ} (ψ : DyadicAtom N → E →L[ℝ] ℝ)
    (φ : DyadicAtom N → E) (j : Fin N) :
    (dyadicLaw N).expect (fun ω => dyadicIncrement ψ j ω (dyadicIncrement φ j ω)) =
      (dyadicLaw j.val).expect (fun α =>
        dyadicCoefficient ψ j α (dyadicCoefficient φ j α)) := by
  have hpoint (ω : DyadicWord N) :
      dyadicIncrement ψ j ω (dyadicIncrement φ j ω) =
        dyadicCoefficient ψ j (dyadicPrefix ω j.val (Nat.le_of_lt j.is_lt))
          (dyadicCoefficient φ j (dyadicPrefix ω j.val (Nat.le_of_lt j.is_lt))) := by
    cases hb : ω j <;> simp [dyadicIncrement, dyadicSign, hb]
  simp_rw [hpoint]
  exact dyadicLaw_expect_prefix (Nat.le_of_lt j.is_lt)
    (fun α => dyadicCoefficient ψ j α (dyadicCoefficient φ j α))

theorem dyadicInputPairing_prefixes {N : ℕ} (ψ : DyadicAtom N → E →L[ℝ] ℝ)
    (φ : DyadicAtom N → E) :
    (∑ a, dyadicInputWeight a * ψ a (φ a)) =
      dyadicRoot ψ (dyadicRoot φ) + ∑ j : Fin N,
        (dyadicLaw j.val).expect (fun α =>
          dyadicCoefficient ψ j α (dyadicCoefficient φ j α)) := by
  classical
  simp only [Fintype.sum_sum_type, Fintype.sum_sigma,
    dyadicInputWeight, dyadicRoot, dyadicCoefficient, FiniteLaw.expect]
  simp

theorem dyadicSynthesis_pairing {N : ℕ} (ψ : DyadicAtom N → E →L[ℝ] ℝ)
    (φ : DyadicAtom N → E) :
    (dyadicLaw N).expect (fun ω => dyadicSynthesis N ψ ω (dyadicSynthesis N φ ω)) =
      ∑ a, dyadicInputWeight a * ψ a (φ a) := by
  let f : ℕ → ℝ := fun j => (dyadicLaw N).expect (fun ω =>
    finiteDifference (dyadicProcess ψ) j ω (finiteDifference (dyadicProcess φ) j ω))
  have hz : f 0 = dyadicRoot ψ (dyadicRoot φ) := by
    simp only [f, finiteDifference_zero, dyadicProcess_zero, FiniteLaw.expect_const]
  have hs (j : Fin N) : f (j.val + 1) =
      (dyadicLaw j.val).expect (fun α =>
        dyadicCoefficient ψ j α (dyadicCoefficient φ j α)) := by
    simpa only [f, dyadicProcess_difference_succ, dite_eq_left j.is_lt] using
      dyadicIncrement_pairing ψ φ j
  calc
    _ = ∑ j ∈ Finset.range (N + 1), f j :=
      finite_martingale_terminal_pairing_of_martingales
        (dyadicProcess_isMartingale ψ N) (dyadicProcess_isMartingale φ N)
    _ = (∑ j : Fin N, f (j.val + 1)) + f 0 := by
      rw [Finset.sum_range_succ',
        Fin.sum_univ_eq_sum_range (fun k : ℕ => f (k + 1)) N]
    _ = dyadicRoot ψ (dyadicRoot φ) + ∑ j : Fin N,
        (dyadicLaw j.val).expect (fun α =>
          dyadicCoefficient ψ j α (dyadicCoefficient φ j α)) := by
      simp only [hs, hz, add_comm]
    _ = _ := (dyadicInputPairing_prefixes ψ φ).symm

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_DyadicTreeMartingale
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {E : Type*} [sectionNormedAddCommGroupE : NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]

theorem dyadicLaw_expect_snoc {n : ℕ} (f : DyadicWord (n + 1) → ℝ) :
    (dyadicLaw (n + 1)).expect f = (dyadicLaw n).expect
      (fun α => (f (Fin.snoc α true) + f (Fin.snoc α false)) / 2) := by
  classical
  unfold FiniteLaw.expect
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp
    (fun ω => (dyadicLaw (n + 1)).mass ω * f ω)]
  rw [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro α _
  change (dyadicLaw (n + 1)).mass (Fin.snoc α true) * f (Fin.snoc α true) +
      (dyadicLaw (n + 1)).mass (Fin.snoc α false) * f (Fin.snoc α false) = _
  simp only [dyadicLaw_mass, pow_succ]
  ring

namespace DyadicTree

theorem root_branch (t : DyadicTree E) (b : Bool) :
    root (branch t b) = root t + dyadicSign b • splitCoefficient t := by
  cases t <;> cases b <;> simp [branch, splitCoefficient, dyadicSign] <;> module

omit sectionNormedSpaceℝE in
theorem moment_branch_average [NormedSpace ℝ E] (t : DyadicTree E) (p : ℝ) :
    (moment p (branch t true) + moment p (branch t false)) / 2 = moment p t := by
  cases t with
  | leaf x => simp only [branch, moment_leaf]; ring
  | node t s => rfl

theorem energy_branch_average {p : ℝ} (hp : 0 < p) (t : DyadicTree E) :
    (energy p (branch t true) + energy p (branch t false)) / 2 +
      ‖splitCoefficient t‖ ^ p = energy p t := by
  cases t with
  | leaf x => simp [branch, splitCoefficient, Real.zero_rpow hp.ne']
  | node t s => rfl

omit sectionNormedAddCommGroupE sectionNormedSpaceℝE in
theorem full_branch [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} {t : DyadicTree E} (h : Full (n + 1) t) (b : Bool) :
    Full n (branch t b) := by
  cases t with
  | leaf x => exact h.elim
  | node t s =>
      cases b with
      | false => exact h.2
      | true => exact h.1

theorem full_descendant {n k : ℕ} {t : DyadicTree E} (h : Full (n + k) t)
    (α : DyadicWord n) : Full k (descendant t n α) := by
  induction n generalizing k with
  | zero => simpa only [Nat.zero_add, descendant] using h
  | succ n ih =>
      apply full_branch
      apply ih (k := k + 1)
      convert h using 1 ; omega

theorem moment_full_zero {t : DyadicTree E} (h : Full 0 t) (p : ℝ) :
    moment p t = ‖root t‖ ^ p := by
  cases t with
  | leaf x => rfl
  | node t s => exact h.elim

theorem energy_full_zero {t : DyadicTree E} (h : Full 0 t) (p : ℝ) :
    energy p t = 0 := by
  cases t with
  | leaf x => rfl
  | node t s => exact h.elim

theorem expect_moment_descendant (t : DyadicTree E) (n : ℕ) (p : ℝ) :
    (dyadicLaw n).expect (fun α => moment p (descendant t n α)) = moment p t := by
  induction n with
  | zero => exact FiniteLaw.expect_const (dyadicLaw 0) (moment p t)
  | succ n ih =>
      rw [dyadicLaw_expect_snoc]
      simp only [descendant_snoc, moment_branch_average]
      exact ih

theorem expected_energy_step {p : ℝ} (hp : 0 < p) (t : DyadicTree E) (n : ℕ) :
    (dyadicLaw (n + 1)).expect (fun α => energy p (descendant t (n + 1) α)) +
      (dyadicLaw n).expect (fun α => ‖splitCoefficient (descendant t n α)‖ ^ p) =
      (dyadicLaw n).expect (fun α => energy p (descendant t n α)) := by
  rw [dyadicLaw_expect_snoc]
  simp only [descendant_snoc, FiniteLaw.expect]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro α _
  rw [← mul_add, energy_branch_average hp]

theorem energy_telescope {p : ℝ} (hp : 0 < p) (t : DyadicTree E) (n : ℕ) :
    (dyadicLaw n).expect (fun α => energy p (descendant t n α)) +
      (∑ j : Fin n, (dyadicLaw j.val).expect
        (fun α => ‖splitCoefficient (descendant t j.val α)‖ ^ p)) = energy p t := by
  induction n with
  | zero => simp [descendant, FiniteLaw.expect_const]
  | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      have hstep := expected_energy_step hp t n
      linarith

theorem process_coefficients {N n : ℕ} (hn : n ≤ N) (t : DyadicTree E)
    (ω : DyadicWord N) :
    dyadicProcess (coefficients N t) n ω = root (descendant t n (dyadicPrefix ω n hn)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hnN : n < N := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn
      have hprev : n ≤ N := Nat.le_of_lt hnN
      simp only [dyadicProcess, dite_eq_left hnN, ih hprev]
      change root (descendant t n (dyadicPrefix ω n hprev)) +
        dyadicSign (ω ⟨n, hnN⟩) • splitCoefficient
          (descendant t n (dyadicPrefix ω n hprev)) = _
      rw [descendant, root_branch]
      rfl

theorem synthesis_coefficients (N : ℕ) (t : DyadicTree E) (ω : DyadicWord N) :
    dyadicSynthesis N (coefficients N t) ω = root (descendant t N ω) := by
  change dyadicProcess (coefficients N t) N ω = _
  rw [process_coefficients (Nat.le_refl N)]
  rfl

theorem synthesis_moment {N : ℕ} {t : DyadicTree E} (h : Full N t) (p : ℝ) :
    finiteMoment (dyadicLaw N).mass p (dyadicSynthesis N (coefficients N t)) = moment p t := by
  have hfull (α : DyadicWord N) : Full 0 (descendant t N α) :=
    full_descendant (k := 0) (by simpa only [Nat.add_zero] using h) α
  calc
    _ = (dyadicLaw N).expect (fun α => moment p (descendant t N α)) := by
      unfold finiteMoment FiniteLaw.expect
      apply Finset.sum_congr rfl
      intro α _
      simp only [synthesis_coefficients, moment_full_zero (hfull α)]
    _ = moment p t := expect_moment_descendant t N p

theorem coefficients_energy {N : ℕ} {t : DyadicTree E} (h : Full N t)
    {p : ℝ} (hp : 0 < p) :
    (∑ j : Fin N, finiteMoment (dyadicLaw N).mass p
      (dyadicIncrement (coefficients N t) j)) = energy p t := by
  have hz : (dyadicLaw N).expect (fun α => energy p (descendant t N α)) = 0 := by
    have hzero : (fun α : DyadicWord N => energy p (descendant t N α)) = fun _ => 0 := by
      funext α
      exact energy_full_zero
        (full_descendant (k := 0) (by simpa only [Nat.add_zero] using h) α) p
    rw [hzero, FiniteLaw.expect_const]
  simpa only [dyadicIncrement_moment, coefficients_prefix, hz, zero_add] using
    energy_telescope hp t N

theorem coefficients_inputMoment {N : ℕ} {t : DyadicTree E} (h : Full N t)
    {p : ℝ} (hp : 0 < p) :
    finiteMoment dyadicInputWeight p (coefficients N t) = ‖root t‖ ^ p + energy p t := by
  rw [dyadicInputMoment, coefficients_root, coefficients_energy h hp]

end DyadicTree
end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteDualNorming
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

theorem exists_unit_test_ge_norm_sub (f : E →L[ℝ] ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x : E, ‖x‖ ≤ 1 ∧ ‖f‖ - ε ≤ f x := by
  obtain ⟨x, hx, hfx⟩ := f.exists_lt_apply_of_lt_opNorm (sub_lt_self ‖f‖ hε)
  by_cases hpos : 0 ≤ f x
  · refine ⟨x, hx.le, ?_⟩
    simpa only [Real.norm_eq_abs, abs_of_nonneg hpos] using hfx.le
  · refine ⟨-x, by simpa only [norm_neg] using hx.le, ?_⟩
    simpa only [map_neg, Real.norm_eq_abs, abs_of_neg (lt_of_not_ge hpos)] using hfx.le

theorem exists_weighted_dual_l2_test (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (f : ι → E →L[ℝ] ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hDsq : D ^ (2 : ℕ) = ∑ i, w i * ‖f i‖ ^ (2 : ℕ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ z : ι → E,
      (∑ i, w i * ‖z i‖ ^ (2 : ℕ)) ≤ 1 ∧
      D - ε ≤ ∑ i, w i * (f i) (z i) := by
  classical
  by_cases hDz : D = 0
  · refine ⟨fun _ => 0, ?_, ?_⟩
    · simp
    · simp only [map_zero, mul_zero, Finset.sum_const_zero, hDz, zero_sub]
      exact neg_nonpos.mpr hε.le
  have hDpos : 0 < D := lt_of_le_of_ne hD (Ne.symm hDz)
  let S : ℝ := ∑ i, w i * ‖f i‖
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (norm_nonneg _)
  have hS1 : 0 < S + 1 := by linarith only [hS]
  let η : ℝ := ε * D / (S + 1)
  have hη : 0 < η := div_pos (mul_pos hε hDpos) hS1
  let u : ι → E := fun i => Classical.choose (exists_unit_test_ge_norm_sub (f i) hη)
  have hu (i : ι) : ‖u i‖ ≤ 1 ∧ ‖f i‖ - η ≤ (f i) (u i) :=
    Classical.choose_spec (exists_unit_test_ge_norm_sub (f i) hη)
  let a : ι → ℝ := fun i => ‖f i‖ / D
  have ha (i : ι) : 0 ≤ a i := div_nonneg (norm_nonneg _) hD
  let z : ι → E := fun i => a i • u i
  have hnorm (i : ι) : ‖z i‖ ≤ a i := by
    calc
      ‖z i‖ = a i * ‖u i‖ := by
        dsimp [z]
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ha i)]
      _ ≤ a i * 1 := mul_le_mul_of_nonneg_left (hu i).1 (ha i)
      _ = a i := mul_one _
  have hnormsq (i : ι) : ‖z i‖ ^ (2 : ℕ) ≤ a i ^ (2 : ℕ) := by
    nlinarith only [hnorm i, norm_nonneg (z i), ha i]
  have hasq : (∑ i, w i * a i ^ (2 : ℕ)) = 1 := by
    calc
      (∑ i, w i * a i ^ (2 : ℕ)) =
          (∑ i, w i * ‖f i‖ ^ (2 : ℕ)) / D ^ (2 : ℕ) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        dsimp [a]
        rw [div_pow, mul_div_assoc]
      _ = 1 := by rw [← hDsq, div_self (pow_ne_zero 2 hDz)]
  have hasum : (∑ i, w i * a i) = S / D := by
    dsimp [a, S]
    simp only [mul_div_assoc, Finset.sum_div]
  have hamoment : (∑ i, w i * a i * ‖f i‖) = D := by
    calc
      (∑ i, w i * a i * ‖f i‖) =
          (∑ i, w i * ‖f i‖ ^ (2 : ℕ)) / D := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        dsimp [a]
        ring
      _ = D := by
        rw [← hDsq]
        field_simp [hDz]
  have hηbound : η * (S / D) ≤ ε := by
    have hratio : S / (S + 1) ≤ 1 := (div_le_one hS1).mpr (by linarith)
    calc
      η * (S / D) = ε * (S / (S + 1)) := by
        dsimp [η]
        field_simp [hDz, hS1.ne']
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hratio hε.le
      _ = ε := mul_one _
  refine ⟨z, ?_, ?_⟩
  · calc
      (∑ i, w i * ‖z i‖ ^ (2 : ℕ)) ≤ ∑ i, w i * a i ^ (2 : ℕ) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hnormsq i) (hw i)
      _ = 1 := hasq
  · have htest : (∑ i, w i * a i * (‖f i‖ - η)) ≤
        ∑ i, w i * (f i) (z i) := by
      apply Finset.sum_le_sum
      intro i _
      have hpoint := mul_le_mul_of_nonneg_left (hu i).2 (mul_nonneg (hw i) (ha i))
      simpa only [z, map_smul, smul_eq_mul, mul_assoc] using hpoint
    have hleft : (∑ i, w i * a i * (‖f i‖ - η)) = D - η * (S / D) := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
      rw [hamoment, hasum]
      ring
    rw [hleft] at htest
    linarith only [htest, hηbound]

omit sectionNormedSpaceℝE in
theorem weighted_norm_rpow_root [NormedSpace ℝ E] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (x : ι → E) {q : ℝ} (hq : 0 < q) :
    ((∑ i, w i * ‖x i‖ ^ q) ^ (1 / q)) ^ q = ∑ i, w i * ‖x i‖ ^ q := by
  have hsum : 0 ≤ ∑ i, w i * ‖x i‖ ^ q :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (Real.rpow_nonneg (norm_nonneg _) _)
  rw [← Real.rpow_mul hsum]
  have hexp : (1 / q) * q = (1 : ℝ) := by field_simp [hq.ne']
  rw [hexp, Real.rpow_one]

theorem exists_weighted_dual_norming (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (x : ι → E) {p q : ℝ} (hpq : p.HolderConjugate q)
    (D : ℝ) (hD : 0 < D) (hDq : D ^ q = ∑ i, w i * ‖x i‖ ^ q) :
    ∃ ψ : ι → E →L[ℝ] ℝ,
      (∑ i, w i * ‖ψ i‖ ^ p) ≤ 1 ∧ (∑ i, w i * ψ i (x i)) = D := by
  classical
  let ell : ι → E →L[ℝ] ℝ := fun i => Classical.choose (exists_dual_vector'' ℝ (x i))
  have hell (i : ι) : ‖ell i‖ ≤ 1 ∧ ell i (x i) = ‖x i‖ :=
    Classical.choose_spec (exists_dual_vector'' ℝ (x i))
  let c : ι → ℝ := fun i => (‖x i‖ / D) ^ (q - 1)
  have hc (i : ι) : 0 ≤ c i := Real.rpow_nonneg (div_nonneg (norm_nonneg _) hD.le) _
  let ψ : ι → E →L[ℝ] ℝ := fun i => c i • ell i
  have hψnorm (i : ι) : ‖ψ i‖ ≤ c i := by
    calc
      ‖ψ i‖ ≤ ‖c i‖ * ‖ell i‖ := ContinuousLinearMap.opNorm_smul_le (c i) (ell i)
      _ = c i * ‖ell i‖ := by rw [Real.norm_eq_abs, abs_of_nonneg (hc i)]
      _ ≤ c i * 1 := mul_le_mul_of_nonneg_left (hell i).1 (hc i)
      _ = c i := mul_one _
  have hcpow (i : ι) : c i ^ p = ‖x i‖ ^ q / D ^ q := by
    dsimp [c]
    rw [← Real.rpow_mul (div_nonneg (norm_nonneg _) hD.le),
      hpq.symm.sub_one_mul_conj, Real.div_rpow (norm_nonneg _) hD.le]
  have hcnorm (i : ι) : c i * ‖x i‖ = ‖x i‖ ^ q / D ^ (q - 1) := by
    have hxpow : ‖x i‖ ^ (q - 1) * ‖x i‖ = ‖x i‖ ^ q := by
      have hexp : q - 1 + 1 = q := by ring
      rw [← Real.rpow_add_one' (y := q - 1) (norm_nonneg _)
        (by simpa only [hexp] using hpq.symm.ne_zero), hexp]
    dsimp [c]
    rw [Real.div_rpow (norm_nonneg _) hD.le]
    calc
      (‖x i‖ ^ (q - 1) / D ^ (q - 1)) * ‖x i‖ =
          (‖x i‖ ^ (q - 1) * ‖x i‖) / D ^ (q - 1) := by ring
      _ = ‖x i‖ ^ q / D ^ (q - 1) := by rw [hxpow]
  refine ⟨ψ, ?_, ?_⟩
  · calc
      (∑ i, w i * ‖ψ i‖ ^ p) ≤ ∑ i, w i * c i ^ p := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (norm_nonneg _) (hψnorm i) hpq.pos.le) (hw i)
      _ = (∑ i, w i * ‖x i‖ ^ q) / D ^ q := by
        simp only [hcpow, mul_div_assoc, Finset.sum_div]
      _ = 1 := by rw [← hDq, div_self (Real.rpow_pos_of_pos hD q).ne']
  · calc
      (∑ i, w i * ψ i (x i)) = ∑ i, w i * (c i * ‖x i‖) := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [ψ, smul_apply, smul_eq_mul, (hell i).2]
      _ = (∑ i, w i * ‖x i‖ ^ q) / D ^ (q - 1) := by
        simp only [hcnorm, mul_div_assoc, Finset.sum_div]
      _ = D := by
        rw [← hDq, ← Real.rpow_sub hD q (q - 1)]
        have hexp : q - (q - 1) = (1 : ℝ) := by ring
        rw [hexp, Real.rpow_one]

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteWeightedHolder
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

variable {ι : Type*}

theorem holder_weight_split {p q w : ℝ} (hpq : p.HolderConjugate q) (hw : 0 ≤ w) :
    w ^ (1 / p) * w ^ (1 / q) = w := by
  have hs : 1 / p + 1 / q = (1 : ℝ) := by simpa using hpq.one_div_add_one_div
  rw [← Real.rpow_add' hw (by rw [hs]; exact one_ne_zero), hs, Real.rpow_one]

theorem weighted_power_root_mul {r w a : ℝ} (hr : r ≠ 0)
    (hw : 0 ≤ w) (ha : 0 ≤ a) :
    (w ^ (1 / r) * a) ^ r = w * a ^ r := by
  rw [Real.mul_rpow (Real.rpow_nonneg hw _) ha, ← Real.rpow_mul hw,
    one_div, inv_mul_cancel₀ hr, Real.rpow_one]

theorem finite_weighted_holder (s : Finset ι) {w a b : ι → ℝ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (hw : ∀ i ∈ s, 0 ≤ w i)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) :
    (∑ i ∈ s, w i * a i * b i) ≤
      (∑ i ∈ s, w i * a i ^ p) ^ (1 / p) *
        (∑ i ∈ s, w i * b i ^ q) ^ (1 / q) := by
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg
    (f := fun i => w i ^ (1 / p) * a i)
    (g := fun i => w i ^ (1 / q) * b i) s hpq
    (fun i hi => mul_nonneg (Real.rpow_nonneg (hw i hi) _) (ha i hi))
    (fun i hi => mul_nonneg (Real.rpow_nonneg (hw i hi) _) (hb i hi))
  have hleft : (∑ i ∈ s, (w i ^ (1 / p) * a i) * (w i ^ (1 / q) * b i)) =
      ∑ i ∈ s, w i * a i * b i := by
    apply Finset.sum_congr rfl
    intro i hi
    calc
      (w i ^ (1 / p) * a i) * (w i ^ (1 / q) * b i) =
          (w i ^ (1 / p) * w i ^ (1 / q)) * a i * b i := by ring
      _ = w i * a i * b i := by rw [holder_weight_split hpq (hw i hi)]
  have hrightp : (∑ i ∈ s, (w i ^ (1 / p) * a i) ^ p) =
      ∑ i ∈ s, w i * a i ^ p := by
    apply Finset.sum_congr rfl
    intro i hi
    exact weighted_power_root_mul hpq.ne_zero (hw i hi) (ha i hi)
  have hrightq : (∑ i ∈ s, (w i ^ (1 / q) * b i) ^ q) =
      ∑ i ∈ s, w i * b i ^ q := by
    apply Finset.sum_congr rfl
    intro i hi
    exact weighted_power_root_mul hpq.symm.ne_zero (hw i hi) (hb i hi)
  rwa [hleft, hrightp, hrightq] at h

theorem finite_weighted_holder_univ [Fintype ι] {w a b : ι → ℝ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (hw : ∀ i, 0 ≤ w i)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    (∑ i, w i * a i * b i) ≤
      (∑ i, w i * a i ^ p) ^ (1 / p) *
        (∑ i, w i * b i ^ q) ^ (1 / q) :=
  finite_weighted_holder Finset.univ hpq
    (fun i _ => hw i) (fun i _ => ha i) (fun i _ => hb i)

theorem abs_sum_weighted_le_holder (s : Finset ι) {w a b c : ι → ℝ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (hw : ∀ i ∈ s, 0 ≤ w i)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i)
    (hc : ∀ i ∈ s, |c i| ≤ a i * b i) :
    |∑ i ∈ s, w i * c i| ≤
      (∑ i ∈ s, w i * a i ^ p) ^ (1 / p) *
        (∑ i ∈ s, w i * b i ^ q) ^ (1 / q) := by
  calc
    |∑ i ∈ s, w i * c i| ≤ ∑ i ∈ s, |w i * c i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, w i * a i * b i := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg (hw i hi)]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hc i hi) (hw i hi)
    _ ≤ _ := finite_weighted_holder s hpq hw ha hb

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_DyadicCotypeDuality
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem dyadicInputMoment_le_of_dual_synthesis {p q T : ℝ}
    (hpq : p.HolderConjugate q) (hT : 1 ≤ T)
    (hStrong : ∀ (N : ℕ) (ψ : DyadicAtom N → E →L[ℝ] ℝ),
      finiteMoment (dyadicLaw N).mass p (dyadicSynthesis N ψ) ≤
        T ^ p * finiteMoment dyadicInputWeight p ψ)
    (N : ℕ) (φ : DyadicAtom N → E) :
    finiteMoment dyadicInputWeight q φ ≤
      T ^ q * finiteMoment (dyadicLaw N).mass q (dyadicSynthesis N φ) := by
  classical
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  let I : ℝ := finiteMoment dyadicInputWeight q φ
  let O : ℝ := finiteMoment (dyadicLaw N).mass q (dyadicSynthesis N φ)
  have hI : 0 ≤ I := Finset.sum_nonneg fun a _ =>
    mul_nonneg (dyadicInputWeight_nonneg a) (Real.rpow_nonneg (norm_nonneg _) q)
  have hO : 0 ≤ O := Finset.sum_nonneg fun ω _ =>
    mul_nonneg ((dyadicLaw N).mass_nonneg ω) (Real.rpow_nonneg (norm_nonneg _) q)
  change I ≤ T ^ q * O
  by_cases hIz : I = 0
  · rw [hIz]
    exact mul_nonneg (Real.rpow_nonneg hT0 q) hO
  have hIpos : 0 < I := lt_of_le_of_ne hI (Ne.symm hIz)
  let D : ℝ := I ^ (1 / q)
  have hD : 0 < D := Real.rpow_pos_of_pos hIpos _
  have hDq : D ^ q = I :=
    weighted_norm_rpow_root dyadicInputWeight dyadicInputWeight_nonneg φ hpq.symm.pos
  obtain ⟨ψ, hψ, hpair⟩ := exists_weighted_dual_norming dyadicInputWeight
    dyadicInputWeight_nonneg φ hpq D hD hDq
  change finiteMoment dyadicInputWeight p ψ ≤ 1 at hψ
  have hM0 : 0 ≤ finiteMoment (dyadicLaw N).mass p (dyadicSynthesis N ψ) :=
    Finset.sum_nonneg fun ω _ => mul_nonneg ((dyadicLaw N).mass_nonneg ω)
      (Real.rpow_nonneg (norm_nonneg _) p)
  have hMoment : finiteMoment (dyadicLaw N).mass p (dyadicSynthesis N ψ) ≤ T ^ p := by
    calc
      _ ≤ T ^ p * finiteMoment dyadicInputWeight p ψ := hStrong N ψ
      _ ≤ T ^ p * 1 := mul_le_mul_of_nonneg_left hψ (Real.rpow_nonneg hT0 p)
      _ = T ^ p := mul_one _
  have hRoot : (finiteMoment (dyadicLaw N).mass p (dyadicSynthesis N ψ)) ^ (1 / p) ≤ T := by
    calc
      _ ≤ (T ^ p) ^ (1 / p) :=
        Real.rpow_le_rpow hM0 hMoment (one_div_pos.mpr hpq.pos).le
      _ = T := by rw [one_div, Real.rpow_rpow_inv hT0 hpq.ne_zero]
  have hPairing : (dyadicLaw N).expect (fun ω =>
      dyadicSynthesis N ψ ω (dyadicSynthesis N φ ω)) = D :=
    (dyadicSynthesis_pairing ψ φ).trans hpair
  have hHolder : |(dyadicLaw N).expect (fun ω =>
      dyadicSynthesis N ψ ω (dyadicSynthesis N φ ω))| ≤
      (finiteMoment (dyadicLaw N).mass p (dyadicSynthesis N ψ)) ^ (1 / p) * O ^ (1 / q) := by
    have hh := abs_sum_weighted_le_holder Finset.univ
      (w := (dyadicLaw N).mass) (a := fun ω => ‖dyadicSynthesis N ψ ω‖)
      (b := fun ω => ‖dyadicSynthesis N φ ω‖)
      (c := fun ω => dyadicSynthesis N ψ ω (dyadicSynthesis N φ ω)) hpq
      (fun ω _ => (dyadicLaw N).mass_nonneg ω) (fun ω _ => norm_nonneg _)
      (fun ω _ => norm_nonneg _) (by
        intro ω _
        simpa only [Real.norm_eq_abs] using
          (dyadicSynthesis N ψ ω).le_opNorm (dyadicSynthesis N φ ω))
    simpa only [FiniteLaw.expect, finiteMoment, O] using hh
  have hDle : D ≤ T * O ^ (1 / q) := by
    rw [hPairing, abs_of_pos hD] at hHolder
    exact hHolder.trans (mul_le_mul_of_nonneg_right hRoot (Real.rpow_nonneg hO _))
  have hOq : (O ^ (1 / q)) ^ q = O :=
    weighted_norm_rpow_root (dyadicLaw N).mass (dyadicLaw N).mass_nonneg
      (dyadicSynthesis N φ) hpq.symm.pos
  have hPower := Real.rpow_le_rpow hD.le hDle hpq.symm.pos.le
  rwa [hDq, Real.mul_rpow hT0 (Real.rpow_nonneg hO _), hOq] at hPower

theorem finiteDyadicCotype_of_dual_synthesis {p q T : ℝ}
    (hpq : p.HolderConjugate q) (hT : 1 ≤ T)
    (hStrong : ∀ (N : ℕ) (ψ : DyadicAtom N → E →L[ℝ] ℝ),
      finiteMoment (dyadicLaw N).mass p (dyadicSynthesis N ψ) ≤
        T ^ p * finiteMoment dyadicInputWeight p ψ) :
    FiniteDyadicCotype E q (T ^ q) := by
  intro t ht
  let N := DyadicTree.height t
  let u := DyadicTree.pad N t
  have hu : DyadicTree.Full N u := DyadicTree.pad_full N t le_rfl
  have h := dyadicInputMoment_le_of_dual_synthesis hpq hT hStrong N
    (DyadicTree.coefficients N u)
  rw [DyadicTree.coefficients_inputMoment hu hpq.symm.pos,
    DyadicTree.synthesis_moment hu q] at h
  simpa only [u, DyadicTree.root_pad, ht, norm_zero, Real.zero_rpow hpq.symm.ne_zero,
    zero_add, DyadicTree.energy_pad hpq.symm.pos, DyadicTree.moment_pad] using h

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_DyadicIndependentBlocks
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem dyadicIndependentBlocks_increment {m N : ℕ} (c : ℝ) (φ : DyadicAtom N → E)
    (j : Fin (m * N)) (ω : DyadicWord (m * N)) :
    dyadicIncrement (dyadicIndependentBlocks m c φ) j ω =
      c • dyadicIncrement φ (finProdFinEquiv.symm j).2
        (dyadicBlockEquiv m N ω (finProdFinEquiv.symm j).1) := by
  simp only [dyadicIncrement, dyadicCoefficient, dyadicIndependentBlocks,
    dyadicBlockPrefix_prefix]
  have hbit : ω j = dyadicBlockEquiv m N ω (finProdFinEquiv.symm j).1
      (finProdFinEquiv.symm j).2 := by
    change ω j = ω (finProdFinEquiv (finProdFinEquiv.symm j))
    rw [Equiv.apply_symm_apply]
  rw [hbit]
  module

theorem dyadicIndependentBlocks_increment_pair {m N : ℕ} (c : ℝ)
    (φ : DyadicAtom N → E) (b : Fin m) (i : Fin N) (ω : DyadicWord (m * N)) :
    dyadicIncrement (dyadicIndependentBlocks m c φ) (finProdFinEquiv (b, i)) ω =
      c • dyadicIncrement φ i (dyadicBlockEquiv m N ω b) := by
  simpa only [Equiv.symm_apply_apply] using
    dyadicIndependentBlocks_increment c φ (finProdFinEquiv (b, i)) ω

theorem dyadicIndependentBlocks_increment_moment {m N : ℕ} (c p : ℝ)
    (φ : DyadicAtom N → E) (b : Fin m) (i : Fin N) :
    finiteMoment (dyadicLaw (m * N)).mass p
      (dyadicIncrement (dyadicIndependentBlocks m c φ) (finProdFinEquiv (b, i))) =
      |c| ^ p * finiteMoment (dyadicLaw N).mass p (dyadicIncrement φ i) := by
  change (dyadicLaw (m * N)).expect (fun ω =>
    ‖dyadicIncrement (dyadicIndependentBlocks m c φ) (finProdFinEquiv (b, i)) ω‖ ^ p) = _
  simp_rw [dyadicIndependentBlocks_increment_pair]
  rw [dyadicBlock_expect_coord b (fun ω => ‖c • dyadicIncrement φ i ω‖ ^ p)]
  simp only [FiniteLaw.expect, finiteMoment, norm_smul, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg c) (norm_nonneg _), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem dyadicIndependentBlocks_inputMoment {N : ℕ} (m : ℕ) (c : ℝ)
    (φ : DyadicAtom N → E) (hroot : dyadicRoot φ = 0) {p : ℝ} (hp : 0 < p) :
    finiteMoment dyadicInputWeight p (dyadicIndependentBlocks m c φ) =
      |c| ^ p * (m : ℝ) * finiteMoment dyadicInputWeight p φ := by
  rw [dyadicInputMoment, dyadicIndependentBlocks_root, norm_zero, Real.zero_rpow hp.ne',
    zero_add, dyadicInputMoment, hroot, norm_zero, Real.zero_rpow hp.ne', zero_add]
  rw [← (finProdFinEquiv : Fin m × Fin N ≃ Fin (m * N)).sum_comp
    (fun j => finiteMoment (dyadicLaw (m * N)).mass p
      (dyadicIncrement (dyadicIndependentBlocks m c φ) j))]
  rw [Fintype.sum_prod_type]
  simp_rw [dyadicIndependentBlocks_increment_moment]
  simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

theorem dyadicIndependentBlocks_process {m N : ℕ} (c : ℝ) (φ : DyadicAtom N → E)
    (hroot : dyadicRoot φ = 0) (b : Fin m) (j : ℕ) (hj : j ≤ N)
    (ω : DyadicWord (m * N)) :
    dyadicProcess (dyadicIndependentBlocks m c φ) (N * b.val + j) ω =
      dyadicProcess (dyadicIndependentBlocks m c φ) (N * b.val) ω +
        c • dyadicProcess φ j (dyadicBlockEquiv m N ω b) := by
  induction j with
  | zero => simp only [dyadicProcess_zero, hroot, smul_zero, add_zero]
  | succ j ih =>
      have hjN : j < N := Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hj
      have hjle : j ≤ N := Nat.le_of_lt hjN
      let i : Fin N := ⟨j, hjN⟩
      have hindex : N * b.val + j < m * N := by
        have h := (finProdFinEquiv (b, i)).is_lt
        change j + N * b.val < m * N at h
        simpa only [Nat.add_comm] using h
      have heq : (⟨N * b.val + j, hindex⟩ : Fin (m * N)) = finProdFinEquiv (b, i) := by
        apply Fin.ext
        change N * b.val + j = j + N * b.val
        omega
      rw [show N * b.val + (j + 1) = (N * b.val + j) + 1 by omega]
      simp only [dyadicProcess, dite_eq_left hindex, ih hjle, heq,
        dyadicIndependentBlocks_increment_pair, dite_eq_left hjN]
      change _ = _ + c • (_ + dyadicIncrement φ i _)
      module

theorem dyadicIndependentBlocks_boundary {m N : ℕ} (c : ℝ) (φ : DyadicAtom N → E)
    (hroot : dyadicRoot φ = 0) (b : Fin m) (ω : DyadicWord (m * N)) :
    c • dyadicSynthesis N φ (dyadicBlockEquiv m N ω b) =
      dyadicProcess (dyadicIndependentBlocks m c φ) (N * (b.val + 1)) ω -
        dyadicProcess (dyadicIndependentBlocks m c φ) (N * b.val) ω := by
  have h := dyadicIndependentBlocks_process c φ hroot b N (Nat.le_refl N) ω
  rw [Nat.mul_add, Nat.mul_one]
  change c • dyadicProcess φ N _ = _
  rw [h, add_sub_cancel_left]

theorem dyadicIndependentBlocks_copy_norm_le {m N : ℕ} (c : ℝ)
    (φ : DyadicAtom N → E) (hroot : dyadicRoot φ = 0) (ω : DyadicWord (m * N))
    {u : ℝ} (hbound : ∀ j : ℕ, j ≤ m * N →
      ‖dyadicProcess (dyadicIndependentBlocks m c φ) j ω‖ ≤ u) (b : Fin m) :
    ‖c • dyadicSynthesis N φ (dyadicBlockEquiv m N ω b)‖ ≤ 2 * u := by
  rw [dyadicIndependentBlocks_boundary c φ hroot]
  have hstart : N * b.val ≤ m * N := by
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_left N (Nat.le_of_lt b.is_lt)
  have hend : N * (b.val + 1) ≤ m * N := by
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_left N (Nat.succ_le_of_lt b.is_lt)
  calc
    _ ≤ ‖dyadicProcess (dyadicIndependentBlocks m c φ) (N * (b.val + 1)) ω‖ +
        ‖dyadicProcess (dyadicIndependentBlocks m c φ) (N * b.val) ω‖ := norm_sub_le _ _
    _ ≤ u + u := add_le_add (hbound _ hend) (hbound _ hstart)
    _ = 2 * u := by ring

theorem dyadicCopyScale_pos {m : ℕ} (hm : 0 < m) (p : ℝ) :
    0 < dyadicCopyScale m p := inv_pos.mpr (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hm) _)

theorem dyadicCopyScale_moment {m : ℕ} (hm : 0 < m) {p : ℝ} (hp : 0 < p) :
    |dyadicCopyScale m p| ^ p * (m : ℝ) = 1 := by
  rw [abs_of_pos (dyadicCopyScale_pos hm p), dyadicCopyScale,
    Real.inv_rpow (Real.rpow_nonneg (Nat.cast_nonneg m) _) p, one_div,
    Real.rpow_inv_rpow (Nat.cast_nonneg m) hp.ne', inv_mul_cancel₀]
  exact_mod_cast hm.ne'

theorem dyadicIndependentBlocks_normalized {N m : ℕ} (hm : 0 < m)
    (φ : DyadicAtom N → E) (hroot : dyadicRoot φ = 0) {p : ℝ} (hp : 0 < p) :
    finiteMoment dyadicInputWeight p (dyadicIndependentBlocks m (dyadicCopyScale m p) φ) =
      finiteMoment dyadicInputWeight p φ := by
  rw [dyadicIndependentBlocks_inputMoment m _ φ hroot hp, dyadicCopyScale_moment hm hp,
    one_mul]

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteTailAmplification
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

theorem one_sub_pow_le_reciprocal_linear {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (m : ℕ) :
    (1 - a) ^ m ≤ 1 / (1 + (m : ℝ) * a) := by
  have hma : 0 ≤ (m : ℝ) * a := mul_nonneg (Nat.cast_nonneg m) ha0
  have hd : 0 < 1 + (m : ℝ) * a := by linarith
  have hb : 0 ≤ 1 - a := sub_nonneg.mpr ha1
  apply (le_div_iff₀ hd).mpr
  calc
    (1 - a) ^ m * (1 + (m : ℝ) * a) ≤ (1 - a) ^ m * (1 + a) ^ m :=
      mul_le_mul_of_nonneg_left
        (one_add_mul_le_pow (by linarith : -2 ≤ a) m) (pow_nonneg hb m)
    _ = ((1 - a) * (1 + a)) ^ m := by rw [mul_pow]
    _ ≤ 1 := pow_le_one₀
      (mul_nonneg hb (by linarith : 0 ≤ 1 + a)) (by nlinarith [sq_nonneg a])

theorem le_inv_nat_of_half_le_one_sub_pow {a : ℝ} {m : ℕ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hm : 0 < m)
    (hhalf : (1 / 2 : ℝ) ≤ (1 - a) ^ m) :
    a ≤ 1 / (m : ℝ) := by
  have hmreal : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hma : 0 ≤ (m : ℝ) * a := mul_nonneg hmreal.le ha0
  have hd : 0 < 1 + (m : ℝ) * a := by linarith
  have hrecip : (1 / 2 : ℝ) ≤ 1 / (1 + (m : ℝ) * a) :=
    hhalf.trans (one_sub_pow_le_reciprocal_linear ha0 ha1 m)
  have hcross := (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hd).mp hrecip
  apply (le_div_iff₀ hmreal).mpr
  nlinarith

theorem tail_bound_of_nat_scale_bound (Q : ℝ → ℝ) {p R : ℝ}
    (hp : 0 < p) (hR : 0 < R)
    (hmono : AntitoneOn Q (Set.Ioi 0))
    (hQone : ∀ t : ℝ, 0 < t → Q t ≤ 1)
    (hscale : ∀ m : ℕ, 0 < m →
      Q (R * (m : ℝ) ^ (1 / p)) ≤ 1 / (m : ℝ)) :
    ∀ t : ℝ, 0 < t → Q t ≤ 2 * R ^ p / t ^ p := by
  intro t ht
  let x : ℝ := (t / R) ^ p
  have hxpos : 0 < x := Real.rpow_pos_of_pos (div_pos ht hR) p
  have hbound : Q t ≤ 2 / x := by
    by_cases hxone : 1 ≤ x
    · let m : ℕ := ⌊x⌋₊
      have hmpos : 0 < m := Nat.floor_pos.mpr hxone
      have hmreal : (0 : ℝ) < m := Nat.cast_pos.mpr hmpos
      have hmone : (1 : ℝ) ≤ m := by
        exact_mod_cast (Nat.succ_le_of_lt hmpos)
      have hmle : (m : ℝ) ≤ x := Nat.floor_le hxpos.le
      have hlt : x < (m : ℝ) + 1 := Nat.lt_floor_add_one x
      have htwom : x ≤ 2 * (m : ℝ) := by linarith
      have hroot : (m : ℝ) ^ (1 / p) ≤ t / R := by
        have hpow := Real.rpow_le_rpow (Nat.cast_nonneg m) hmle
          (le_of_lt (one_div_pos.mpr hp))
        simpa only [x, one_div, Real.rpow_rpow_inv (div_nonneg ht.le hR.le) hp.ne']
          using hpow
      have hthreshold : R * (m : ℝ) ^ (1 / p) ≤ t := by
        simpa only [mul_comm] using (le_div_iff₀ hR).mp hroot
      have hthreshold_pos : 0 < R * (m : ℝ) ^ (1 / p) :=
        mul_pos hR (Real.rpow_pos_of_pos hmreal _)
      have hrecip : 1 / (m : ℝ) ≤ 2 / x :=
        (div_le_div_iff₀ hmreal hxpos).mpr (by simpa only [one_mul] using htwom)
      exact ((hmono hthreshold_pos ht hthreshold).trans (hscale m hmpos)).trans hrecip
    · have hxlt : x < 1 := lt_of_not_ge hxone
      have hone : (1 : ℝ) ≤ 2 / x := (le_div_iff₀ hxpos).mpr (by linarith)
      exact (hQone t ht).trans hone
  calc
    Q t ≤ 2 / x := hbound
    _ = 2 * R ^ p / t ^ p := by
      dsimp only [x]
      rw [Real.div_rpow ht.le hR.le p, div_div_eq_mul_div]

theorem tail_bound_of_half_power_scale (Q : ℝ → ℝ) {p R : ℝ}
    (hp : 0 < p) (hR : 0 < R)
    (hmono : AntitoneOn Q (Set.Ioi 0))
    (hQnonneg : ∀ t : ℝ, 0 < t → 0 ≤ Q t)
    (hQone : ∀ t : ℝ, 0 < t → Q t ≤ 1)
    (hscale : ∀ m : ℕ, 0 < m →
      (1 / 2 : ℝ) ≤ (1 - Q (R * (m : ℝ) ^ (1 / p))) ^ m) :
    ∀ t : ℝ, 0 < t → Q t ≤ 2 * R ^ p / t ^ p := by
  apply tail_bound_of_nat_scale_bound Q hp hR hmono hQone
  intro m hm
  have hthreshold_pos : 0 < R * (m : ℝ) ^ (1 / p) :=
    mul_pos hR (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hm) _)
  exact le_inv_nat_of_half_le_one_sub_pow
    (hQnonneg _ hthreshold_pos) (hQone _ hthreshold_pos) hm (hscale m hm)

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_DyadicWeakAmplification
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

theorem prob_nonneg (μ : FiniteLaw Ω) (A : Ω → Prop) : 0 ≤ μ.prob A := by
  classical
  exact Finset.sum_nonneg fun ω _ => by
    split_ifs <;> first | exact μ.mass_nonneg ω | exact le_rfl

theorem prob_mono (μ : FiniteLaw Ω) {A B : Ω → Prop} (h : ∀ ω, A ω → B ω) :
    μ.prob A ≤ μ.prob B := by
  classical
  apply Finset.sum_le_sum
  intro ω _
  by_cases ha : A ω
  · simp only [ite_eq_left ha, ite_eq_left (h ω ha)]
    exact le_rfl
  · simp only [ite_eq_right ha]
    split_ifs <;> first | exact μ.mass_nonneg ω | exact le_rfl

theorem prob_le_one (μ : FiniteLaw Ω) (A : Ω → Prop) : μ.prob A ≤ 1 := by
  simpa only [prob_true] using μ.prob_mono (B := fun _ => True) (fun _ _ => trivial)

end FiniteLaw

theorem dyadicAmplificationThreshold_pos {a A : ℝ} (hA : 1 ≤ A) :
    0 < dyadicAmplificationThreshold a A :=
  Real.rpow_pos_of_pos (by linarith) _

theorem dyadicAmplificationRadius_pos {a A : ℝ} (hA : 1 ≤ A) :
    0 < dyadicAmplificationRadius a A :=
  mul_pos (by norm_num) (dyadicAmplificationThreshold_pos hA)

theorem dyadicAmplificationThreshold_power {a A : ℝ} (ha : 0 < a) (hA : 1 ≤ A) :
    (dyadicAmplificationThreshold a A) ^ (a / 2) = 2 * A := by
  unfold dyadicAmplificationThreshold
  rw [← Real.rpow_mul (by linarith : 0 ≤ 2 * A)]
  rw [show (2 / a) * (a / 2) = 1 by field_simp [ha.ne'], Real.rpow_one]

theorem dyadicZeroWeakConstant_ge_one {a A : ℝ} (ha : 0 < a) (hA : 1 ≤ A) :
    1 ≤ dyadicZeroWeakConstant a A := by
  have hu : 1 ≤ dyadicAmplificationThreshold a A :=
    Real.one_le_rpow (by linarith) (div_nonneg (by norm_num) ha.le)
  have hR : 1 ≤ dyadicAmplificationRadius a A := by
    unfold dyadicAmplificationRadius
    linarith
  have hRp := Real.one_le_rpow hR ha.le
  unfold dyadicZeroWeakConstant
  linarith

theorem dyadic_half_power_scale {a A : ℝ} (ha : 0 < a) (hA : 1 ≤ A)
    (hmax : DyadicNormalizedWeakMax E a A) {N : ℕ} (φ : DyadicAtom N → E)
    (hroot : dyadicRoot φ = 0) (hinput : finiteMoment dyadicInputWeight a φ ≤ 1)
    (m : ℕ) (hm : 0 < m) :
    (1 / 2 : ℝ) ≤ (1 - (dyadicLaw N).prob (fun ω =>
      dyadicAmplificationRadius a A * (m : ℝ) ^ (1 / a) < ‖dyadicSynthesis N φ ω‖)) ^ m := by
  classical
  let u := dyadicAmplificationThreshold a A
  let G := dyadicIndependentBlocks m (dyadicCopyScale m a) φ
  let bad : DyadicWord (m * N) → Prop :=
    fun ω => ∃ j : ℕ, j ≤ m * N ∧ u < ‖dyadicProcess G j ω‖
  have hu : 0 < u := dyadicAmplificationThreshold_pos hA
  have hGinput : finiteMoment dyadicInputWeight a G ≤ 1 := by
    dsimp only [G]
    rw [dyadicIndependentBlocks_normalized hm φ hroot ha]
    exact hinput
  have hbad : (dyadicLaw (m * N)).prob bad ≤ 1 / 2 := by
    have hh := hmax (m * N) G (dyadicIndependentBlocks_root _ _ _) hGinput u hu
    have hpow : u ^ (a / 2) = 2 * A := dyadicAmplificationThreshold_power ha hA
    have hApos : 0 < A := by linarith
    have hratio : A / (2 * A) = (1 / 2 : ℝ) := by field_simp [hApos.ne']
    simpa only [hpow, hratio] using hh
  have hgood : (1 / 2 : ℝ) ≤ (dyadicLaw (m * N)).prob (fun ω => ¬ bad ω) := by
    rw [FiniteLaw.prob_not]
    linarith
  have hsub : (dyadicLaw (m * N)).prob (fun ω => ¬ bad ω) ≤
      (dyadicLaw (m * N)).prob (fun ω => ∀ b : Fin m,
        ‖dyadicSynthesis N φ (dyadicBlockEquiv m N ω b)‖ ≤
          dyadicAmplificationRadius a A * (m : ℝ) ^ (1 / a)) := by
    apply FiniteLaw.prob_mono
    intro ω hω b
    have hb : ∀ j : ℕ, j ≤ m * N → ‖dyadicProcess G j ω‖ ≤ u := by
      intro j hj
      exact le_of_not_gt (fun hh => hω ⟨j, hj, hh⟩)
    have hcopy := dyadicIndependentBlocks_copy_norm_le
      (dyadicCopyScale m a) φ hroot ω hb b
    have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
    have hpowpos : 0 < (m : ℝ) ^ (1 / a) := Real.rpow_pos_of_pos hmpos _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (dyadicCopyScale_pos hm a)] at hcopy
    have hdiv : ‖dyadicSynthesis N φ (dyadicBlockEquiv m N ω b)‖ /
        (m : ℝ) ^ (1 / a) ≤ 2 * u := by
      simpa only [dyadicCopyScale, div_eq_mul_inv, mul_comm] using hcopy
    exact (div_le_iff₀ hpowpos).mp hdiv
  have heq : (dyadicLaw (m * N)).prob (fun ω => ∀ b : Fin m,
        ‖dyadicSynthesis N φ (dyadicBlockEquiv m N ω b)‖ ≤
          dyadicAmplificationRadius a A * (m : ℝ) ^ (1 / a)) =
      (1 - (dyadicLaw N).prob (fun ω =>
        dyadicAmplificationRadius a A * (m : ℝ) ^ (1 / a) < ‖dyadicSynthesis N φ ω‖)) ^ m := by
    rw [dyadicBlock_prob m N (fun x => ∀ b : Fin m,
      ‖dyadicSynthesis N φ (x b)‖ ≤ dyadicAmplificationRadius a A * (m : ℝ) ^ (1 / a))]
    exact FiniteLaw.independentCopies_prob_all_norm_le (dyadicLaw N) m
      (dyadicSynthesis N φ) (dyadicAmplificationRadius a A * (m : ℝ) ^ (1 / a))
  exact heq ▸ hgood.trans hsub

theorem dyadic_normalized_zero_tail {a A : ℝ} (ha : 0 < a) (hA : 1 ≤ A)
    (hmax : DyadicNormalizedWeakMax E a A) {N : ℕ} (φ : DyadicAtom N → E)
    (hroot : dyadicRoot φ = 0) (hinput : finiteMoment dyadicInputWeight a φ ≤ 1)
    (t : ℝ) (ht : 0 < t) :
    (dyadicLaw N).prob (fun ω => t < ‖dyadicSynthesis N φ ω‖) ≤
      dyadicZeroWeakConstant a A / t ^ a := by
  apply tail_bound_of_half_power_scale
    (fun s => (dyadicLaw N).prob (fun ω => s < ‖dyadicSynthesis N φ ω‖))
    ha (dyadicAmplificationRadius_pos hA)
    (fun s hs v hv hsv => (dyadicLaw N).prob_mono (fun ω h => hsv.trans_lt h))
    (fun _ _ => FiniteLaw.prob_nonneg _ _) (fun _ _ => FiniteLaw.prob_le_one _ _)
    (fun m hm => dyadic_half_power_scale ha hA hmax φ hroot hinput m hm) t ht

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_DyadicWeakType
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {E : Type*} [NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]

omit sectionNormedSpaceℝE in
theorem finiteMoment_nonneg [NormedSpace ℝ E] {I : Type*} [Fintype I] (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (a : ℝ) (φ : I → E) : 0 ≤ finiteMoment w a φ := by
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (Real.rpow_nonneg (norm_nonneg _) _)

theorem finiteMoment_smul {I : Type*} [Fintype I] (w : I → ℝ)
    (a c : ℝ) (φ : I → E) :
    finiteMoment w a (c • φ) = |c| ^ a * finiteMoment w a φ := by
  unfold finiteMoment
  simp_rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg c) (norm_nonneg _)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem dyadicInputWeight_pos {N : ℕ} (i : DyadicAtom N) :
    0 < dyadicInputWeight i := by
  cases i with
  | inl u => exact zero_lt_one
  | inr z =>
      change 0 < (dyadicLaw z.1.val).mass z.2
      rw [dyadicLaw_mass]
      exact pow_pos (inv_pos.mpr (by norm_num)) _

omit sectionNormedSpaceℝE in
theorem dyadic_eq_zero_of_inputMoment_eq_zero [NormedSpace ℝ E] {a : ℝ} (_ha : 0 < a)
    {N : ℕ} (φ : DyadicAtom N → E)
    (hφ : finiteMoment dyadicInputWeight a φ = 0) : φ = 0 := by
  classical
  funext i
  have hterm : dyadicInputWeight i * ‖φ i‖ ^ a ≤ 0 := by
    rw [← hφ]
    exact Finset.single_le_sum
      (fun j _ => mul_nonneg (dyadicInputWeight_nonneg j)
        (Real.rpow_nonneg (norm_nonneg _) _)) (Finset.mem_univ i)
  have hzero : dyadicInputWeight i * ‖φ i‖ ^ a = 0 :=
    le_antisymm hterm (mul_nonneg (dyadicInputWeight_nonneg i)
      (Real.rpow_nonneg (norm_nonneg _) _))
  have hp : ‖φ i‖ ^ a = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (dyadicInputWeight_pos i).ne'
  exact norm_eq_zero.mp ((Real.rpow_eq_zero_iff_of_nonneg (norm_nonneg _)).mp hp).1

theorem dyadicInputMoment_center {a : ℝ} (ha : 0 < a)
    {N : ℕ} (φ : DyadicAtom N → E) :
    finiteMoment dyadicInputWeight a φ = ‖dyadicRoot φ‖ ^ a +
      finiteMoment dyadicInputWeight a (dyadicCenter φ) := by
  rw [dyadicInputMoment_prefixes φ a, dyadicInputMoment_prefixes (dyadicCenter φ) a]
  simp only [dyadicRoot_center, norm_zero, Real.zero_rpow ha.ne', zero_add,
    dyadicCoefficient_center]

theorem dyadicProcess_center {N : ℕ} (φ : DyadicAtom N → E)
    (n : ℕ) (ω : DyadicWord N) :
    dyadicProcess φ n ω = dyadicRoot φ + dyadicProcess (dyadicCenter φ) n ω := by
  induction n with
  | zero => simp only [dyadicProcess_zero, dyadicRoot_center, add_zero]
  | succ n ih =>
      simp only [dyadicProcess, ih]
      by_cases hn : n < N
      · simp only [dite_eq_left hn, dyadicIncrement, dyadicCoefficient_center, add_assoc]
      · simp only [dite_eq_right hn, add_zero]

theorem dyadicSynthesis_center {N : ℕ} (φ : DyadicAtom N → E) (ω : DyadicWord N) :
    dyadicSynthesis N φ ω =
      dyadicRoot φ + dyadicSynthesis N (dyadicCenter φ) ω :=
  dyadicProcess_center φ N ω

theorem dyadic_zero_tail {a A : ℝ} (ha : 0 < a) (hA : 1 ≤ A)
    (hmax : DyadicNormalizedWeakMax E a A) {N : ℕ} (φ : DyadicAtom N → E)
    (hroot : dyadicRoot φ = 0) (t : ℝ) (ht : 0 < t) :
    (dyadicLaw N).prob (fun ω => t < ‖dyadicSynthesis N φ ω‖) ≤
      dyadicZeroWeakConstant a A * finiteMoment dyadicInputWeight a φ / t ^ a := by
  classical
  let S := finiteMoment dyadicInputWeight a φ
  have hS0 : 0 ≤ S := finiteMoment_nonneg _ dyadicInputWeight_nonneg _ _
  by_cases hS : S = 0
  · have hzero := dyadic_eq_zero_of_inputMoment_eq_zero ha φ hS
    rw [show finiteMoment dyadicInputWeight a φ = 0 from hS, mul_zero, zero_div]
    simp [hzero, FiniteLaw.prob, not_lt.mpr ht.le]
  · have hSpos : 0 < S := lt_of_le_of_ne hS0 (Ne.symm hS)
    let R := S ^ (1 / a)
    have hR : 0 < R := Real.rpow_pos_of_pos hSpos _
    have hRa : R ^ a = S := by
      simpa only [R, one_div] using Real.rpow_inv_rpow hS0 ha.ne'
    have hc : 0 < R⁻¹ := inv_pos.mpr hR
    have hscaled : finiteMoment dyadicInputWeight a (R⁻¹ • φ) ≤ 1 := by
      rw [finiteMoment_smul, abs_of_pos hc, Real.inv_rpow hR.le, hRa]
      change S⁻¹ * S ≤ 1
      rw [inv_mul_cancel₀ hS]
    have hscaledroot : dyadicRoot (R⁻¹ • φ) = 0 := by
      change R⁻¹ • dyadicRoot φ = 0
      rw [hroot, smul_zero]
    have hevent : (fun ω => t < ‖dyadicSynthesis N φ ω‖) =
        (fun ω => R⁻¹ * t < ‖dyadicSynthesis N (R⁻¹ • φ) ω‖) := by
      funext ω
      apply propext
      change (t < ‖dyadicProcess φ N ω‖) ↔
        R⁻¹ * t < ‖dyadicProcess (R⁻¹ • φ) N ω‖
      rw [dyadicProcess_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
      exact (mul_lt_mul_iff_right₀ hc).symm
    rw [hevent]
    calc
      _ ≤ dyadicZeroWeakConstant a A / (R⁻¹ * t) ^ a :=
        dyadic_normalized_zero_tail ha hA hmax _ hscaledroot hscaled _ (mul_pos hc ht)
      _ = dyadicZeroWeakConstant a A * finiteMoment dyadicInputWeight a φ / t ^ a := by
        rw [Real.mul_rpow hc.le ht.le, Real.inv_rpow hR.le, hRa]
        change _ = dyadicZeroWeakConstant a A * S / t ^ a
        have hta : t ^ a ≠ 0 := (Real.rpow_pos_of_pos ht a).ne'
        field_simp [hS, hta]

theorem dyadicWeakConstant_pos {a A : ℝ} (ha : 0 < a) (hA : 1 ≤ A) :
    0 < dyadicWeakConstant a A :=
  mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (lt_of_lt_of_le zero_lt_one (dyadicZeroWeakConstant_ge_one ha hA))

theorem dyadicWeakNorm_pos {a A : ℝ} (ha : 0 < a) (hA : 1 ≤ A) :
    0 < dyadicWeakNorm a A := Real.rpow_pos_of_pos (dyadicWeakConstant_pos ha hA) _

theorem dyadicWeakNorm_power {a A : ℝ} (ha : 0 < a) (hA : 1 ≤ A) :
    dyadicWeakNorm a A ^ a = dyadicWeakConstant a A := by
  simpa only [dyadicWeakNorm, one_div] using
    Real.rpow_inv_rpow (dyadicWeakConstant_pos ha hA).le ha.ne'

theorem dyadic_tail {a A : ℝ} (ha : 0 < a) (hA : 1 ≤ A)
    (hmax : DyadicNormalizedWeakMax E a A) {N : ℕ} (φ : DyadicAtom N → E)
    (t : ℝ) (ht : 0 < t) :
    (dyadicLaw N).prob (fun ω => t < ‖dyadicSynthesis N φ ω‖) ≤
      dyadicWeakConstant a A * finiteMoment dyadicInputWeight a φ / t ^ a := by
  have hta : 0 < t ^ a := Real.rpow_pos_of_pos ht _
  have htwo : 0 < (2 : ℝ) ^ a := Real.rpow_pos_of_pos (by norm_num) _
  have hC : 1 ≤ dyadicZeroWeakConstant a A := dyadicZeroWeakConstant_ge_one ha hA
  have hwhole : 0 ≤ finiteMoment dyadicInputWeight a φ :=
    finiteMoment_nonneg _ dyadicInputWeight_nonneg _ _
  have hcenter : 0 ≤ finiteMoment dyadicInputWeight a (dyadicCenter φ) :=
    finiteMoment_nonneg _ dyadicInputWeight_nonneg _ _
  have hrootle : ‖dyadicRoot φ‖ ^ a ≤ finiteMoment dyadicInputWeight a φ := by
    rw [dyadicInputMoment_center ha φ]
    exact le_add_of_nonneg_right hcenter
  have hcenterle : finiteMoment dyadicInputWeight a (dyadicCenter φ) ≤
      finiteMoment dyadicInputWeight a φ := by
    rw [dyadicInputMoment_center ha φ]
    exact le_add_of_nonneg_left (Real.rpow_nonneg (norm_nonneg _) _)
  by_cases hlarge : t / 2 < ‖dyadicRoot φ‖
  · have hp : (t / 2) ^ a ≤ ‖dyadicRoot φ‖ ^ a :=
      Real.rpow_le_rpow (by positivity) hlarge.le ha.le
    rw [Real.div_rpow ht.le (by norm_num) a] at hp
    have hrootpower : t ^ a ≤ (2 : ℝ) ^ a * ‖dyadicRoot φ‖ ^ a := by
      simpa only [mul_comm] using (div_le_iff₀ htwo).mp hp
    have hmul : finiteMoment dyadicInputWeight a φ ≤
        dyadicZeroWeakConstant a A * finiteMoment dyadicInputWeight a φ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hC hwhole
    calc
      _ ≤ 1 := (dyadicLaw N).prob_le_one _
      _ ≤ dyadicWeakConstant a A * finiteMoment dyadicInputWeight a φ / t ^ a := by
        apply (le_div_iff₀ hta).mpr
        simp only [one_mul, dyadicWeakConstant]
        calc
          t ^ a ≤ (2 : ℝ) ^ a * ‖dyadicRoot φ‖ ^ a := hrootpower
          _ ≤ (2 : ℝ) ^ a * finiteMoment dyadicInputWeight a φ :=
            mul_le_mul_of_nonneg_left hrootle htwo.le
          _ ≤ (2 : ℝ) ^ a * (dyadicZeroWeakConstant a A *
                finiteMoment dyadicInputWeight a φ) :=
            mul_le_mul_of_nonneg_left hmul htwo.le
          _ = _ := by ring
  · have hevent : ∀ ω, t < ‖dyadicSynthesis N φ ω‖ →
        t / 2 < ‖dyadicSynthesis N (dyadicCenter φ) ω‖ := by
      intro ω hω
      rw [dyadicSynthesis_center] at hω
      have hn := norm_add_le (dyadicRoot φ) (dyadicSynthesis N (dyadicCenter φ) ω)
      have hr := not_lt.mp hlarge
      linarith
    calc
      _ ≤ (dyadicLaw N).prob (fun ω => t / 2 < ‖dyadicSynthesis N (dyadicCenter φ) ω‖) :=
        (dyadicLaw N).prob_mono hevent
      _ ≤ dyadicZeroWeakConstant a A *
            finiteMoment dyadicInputWeight a (dyadicCenter φ) / (t / 2) ^ a :=
        dyadic_zero_tail ha hA hmax _ (dyadicRoot_center φ) _ (by positivity)
      _ = dyadicWeakConstant a A *
            finiteMoment dyadicInputWeight a (dyadicCenter φ) / t ^ a := by
        rw [Real.div_rpow ht.le (by norm_num) a]
        unfold dyadicWeakConstant
        field_simp [hta.ne', htwo.ne']
      _ ≤ dyadicWeakConstant a A * finiteMoment dyadicInputWeight a φ / t ^ a :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcenterle (dyadicWeakConstant_pos ha hA).le) hta.le

theorem dyadic_weak_type {a A : ℝ} (ha : 0 < a) (hA : 1 ≤ A)
    (hmax : DyadicNormalizedWeakMax E a A) (N : ℕ) :
    FiniteWeakType dyadicInputWeight (dyadicLaw N).mass (dyadicSynthesis (E := E) N)
      a (dyadicWeakNorm a A) := by
  intro φ t ht
  change (dyadicLaw N).prob (fun ω => t < ‖dyadicSynthesis N φ ω‖) ≤ _
  convert dyadic_tail ha hA hmax φ t ht using 1
  rw [Real.div_rpow (dyadicWeakNorm_pos ha hA).le ht.le,
    dyadicWeakNorm_power ha hA]
  ring

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_DyadicInterpolation
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem dyadicInterpolationConstant_pos {a₀ p a₁ B₀ B₁ : ℝ}
    (ha₀ : 0 < a₀) (ha₀p : a₀ < p) (hpa₁ : p < a₁)
    (hB₀ : 0 < B₀) (hB₁ : 0 < B₁) :
    0 < dyadicInterpolationConstant a₀ p a₁ B₀ B₁ := by
  unfold dyadicInterpolationConstant
  exact mul_pos (ha₀.trans ha₀p) (add_pos
    (div_pos (Real.rpow_pos_of_pos (mul_pos (by norm_num) hB₀) _) (sub_pos.mpr ha₀p))
    (div_pos (Real.rpow_pos_of_pos (mul_pos (by norm_num) hB₁) _) (sub_pos.mpr hpa₁)))

theorem dyadic_strong_of_weak_types {a₀ p a₁ B₀ B₁ : ℝ}
    (ha₀ : 0 < a₀) (ha₀p : a₀ < p) (hpa₁ : p < a₁)
    (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁)
    (h₀ : ∀ N : ℕ, FiniteWeakType dyadicInputWeight (dyadicLaw N).mass
      (dyadicSynthesis N (E := E)) a₀ B₀)
    (h₁ : ∀ N : ℕ, FiniteWeakType dyadicInputWeight (dyadicLaw N).mass
      (dyadicSynthesis N (E := E)) a₁ B₁)
    (N : ℕ) (φ : DyadicAtom N → E) :
    finiteMoment (dyadicLaw N).mass p (dyadicSynthesis N φ) ≤
      dyadicInterpolationConstant a₀ p a₁ B₀ B₁ * finiteMoment dyadicInputWeight p φ :=
  finite_marcinkiewicz dyadicInputWeight dyadicInputWeight_nonneg (dyadicLaw N).mass
    (dyadicLaw N).mass_nonneg (dyadicSynthesis N)
    ha₀ ha₀p hpa₁ hB₀ hB₁ (h₀ N) (h₁ N) φ

theorem dyadic_strong_of_weak_family {p r : ℝ}
    (hp : 1 < p) (hpr : p < r)
    (hweak : ∀ a : ℝ, 1 < a → a < r → ∃ B : ℝ, 0 < B ∧
      ∀ N : ℕ, FiniteWeakType dyadicInputWeight (dyadicLaw N).mass
        (dyadicSynthesis N (E := E)) a B) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (φ : DyadicAtom N → E),
      finiteMoment (dyadicLaw N).mass p (dyadicSynthesis N φ) ≤
        K * finiteMoment dyadicInputWeight p φ := by
  let a₀ := (1 + p) / 2
  let a₁ := (p + r) / 2
  have ha₀one : 1 < a₀ := by dsimp [a₀]; linarith
  have ha₀p : a₀ < p := by dsimp [a₀]; linarith
  have hpa₁ : p < a₁ := by dsimp [a₁]; linarith
  have ha₁r : a₁ < r := by dsimp [a₁]; linarith
  have ha₀ : 0 < a₀ := by linarith
  obtain ⟨B₀, hB₀, h₀⟩ := hweak a₀ ha₀one (ha₀p.trans hpr)
  obtain ⟨B₁, hB₁, h₁⟩ := hweak a₁ (hp.trans hpa₁) ha₁r
  exact ⟨dyadicInterpolationConstant a₀ p a₁ B₀ B₁,
    dyadicInterpolationConstant_pos ha₀ ha₀p hpa₁ hB₀ hB₁,
    dyadic_strong_of_weak_types ha₀ ha₀p hpa₁
      hB₀.le hB₁.le h₀ h₁⟩

theorem dyadic_strong_of_normalizedWeakMax {p r : ℝ}
    (hp : 1 < p) (hpr : p < r)
    (hmax : ∀ a : ℝ, 1 < a → a < r →
      ∃ A : ℝ, 1 ≤ A ∧ DyadicNormalizedWeakMax E a A) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (φ : DyadicAtom N → E),
      finiteMoment (dyadicLaw N).mass p (dyadicSynthesis N φ) ≤
        K * finiteMoment dyadicInputWeight p φ := by
  apply dyadic_strong_of_weak_family hp hpr
  intro a ha har
  obtain ⟨A, hA, hmaxA⟩ := hmax a ha har
  have ha0 : 0 < a := by linarith
  refine ⟨dyadicWeakNorm a A, dyadicWeakNorm_pos ha0 hA, ?_⟩
  exact fun N => dyadic_weak_type ha0 hA hmaxA N

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteGeometricBands
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

theorem half_pow_antitone : Antitone (fun k : ℕ => (1 / 2 : ℝ) ^ k) := by
  apply antitone_nat_of_succ_le
  intro k
  rw [pow_succ]
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) k]

theorem dyadicMagnitudeBand_exists {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    ∃ k : ℕ, dyadicMagnitudeBand k z :=
  exists_nat_pow_near_of_lt_one hz hz1 (by norm_num) (by norm_num)

theorem dyadicMagnitudeBand_unique {k l : ℕ} {z : ℝ}
    (hk : dyadicMagnitudeBand k z) (hl : dyadicMagnitudeBand l z) : k = l := by
  have hkl : ¬k < l := by
    intro h
    have hs := half_pow_antitone (Nat.succ_le_of_lt h)
    exact (not_lt_of_ge (hl.2.trans hs)) hk.1
  have hlk : ¬l < k := by
    intro h
    have hs := half_pow_antitone (Nat.succ_le_of_lt h)
    exact (not_lt_of_ge (hk.2.trans hs)) hl.1
  omega

theorem finite_dyadicMagnitudeBand_cutoff {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, w i ≤ 1) :
    ∃ K : ℕ, ∀ i, 0 < w i → ∃ k ≤ K, dyadicMagnitudeBand k (w i) := by
  let band : ι → ℕ := fun i =>
    if h : 0 < w i then Classical.choose (dyadicMagnitudeBand_exists h (hw i)) else 0
  refine ⟨Finset.univ.sup band, ?_⟩
  intro i hi
  refine ⟨band i, Finset.le_sup (Finset.mem_univ i), ?_⟩
  simp only [band, dite_eq_left hi]
  exact Classical.choose_spec (dyadicMagnitudeBand_exists hi (hw i))

theorem dyadicMagnitudeBand_card_lt {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i ≤ 1) (k : ℕ) :
    (s.filter (fun i => dyadicMagnitudeBand k (w i))).card < 2 ^ (k + 1) := by
  classical
  let u := s.filter (fun i => dyadicMagnitudeBand k (w i))
  by_contra hnot
  have hcard : 2 ^ (k + 1) ≤ u.card := Nat.le_of_not_gt hnot
  have hcardpos : 0 < u.card := (pow_pos (by decide : (0 : ℕ) < 2) (k + 1)).trans_le hcard
  have hu : u.Nonempty := Finset.card_pos.mp hcardpos
  have hlt : (∑ i ∈ u, (1 / 2 : ℝ) ^ (k + 1)) < ∑ i ∈ u, w i :=
    Finset.sum_lt_sum_of_nonempty hu (fun i hi => (Finset.mem_filter.mp hi).2.1)
  have hsumu : (∑ i ∈ u, w i) ≤ 1 := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i hi _ => hw i hi)) hsum
  have hcardreal : (2 : ℝ) ^ (k + 1) ≤ (u.card : ℝ) := by exact_mod_cast hcard
  have hmul := mul_le_mul_of_nonneg_right hcardreal
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (k + 1))
  have hunit : (2 : ℝ) ^ (k + 1) * (1 / 2 : ℝ) ^ (k + 1) = 1 := by
    rw [← mul_pow]
    norm_num
  rw [hunit] at hmul
  have hleft : (∑ i ∈ u, (1 / 2 : ℝ) ^ (k + 1)) =
      (u.card : ℝ) * (1 / 2 : ℝ) ^ (k + 1) := by simp
  rw [hleft] at hlt
  linarith

theorem norm_le_band_bound {E : Type*} [NormedAddCommGroup E]
    {a : ℝ} (ha : 0 < a) {k : ℕ} {x : E}
    (hx : dyadicMagnitudeBand k (‖x‖ ^ a)) :
    ‖x‖ ≤ ((1 / 2 : ℝ) ^ k) ^ (1 / a) := by
  have h := Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg x) a) hx.2
    (one_div_nonneg.mpr ha.le)
  simpa only [one_div, Real.rpow_rpow_inv (norm_nonneg x) ha.ne'] using h

theorem bandGeometricRatio_pos (a r : ℝ) : 0 < bandGeometricRatio a r :=
  mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos (by norm_num) _)

theorem bandGeometricRatio_lt_one {a r : ℝ} (ha : 0 < a) (har : a < r) :
    bandGeometricRatio a r < 1 := by
  have hexp : 1 / r < 1 / a := one_div_lt_one_div_of_lt ha har
  have hpow := Real.rpow_lt_rpow_of_exponent_gt
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1) hexp
  have hmul := mul_lt_mul_of_pos_left hpow
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (1 / r))
  have hunit : (2 : ℝ) ^ (1 / r) * (1 / 2 : ℝ) ^ (1 / r) = 1 := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num
  exact hmul.trans_eq hunit

theorem band_length_times_size (a r : ℝ) (k : ℕ) :
    ((2 ^ (k + 1) : ℕ) : ℝ) ^ (1 / r) * ((1 / 2 : ℝ) ^ k) ^ (1 / a) =
      (2 : ℝ) ^ (1 / r) * bandGeometricRatio a r ^ k := by
  rw [Nat.cast_pow, Nat.cast_ofNat, pow_succ,
    Real.mul_rpow (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k)
      (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  simp only [bandGeometricRatio, mul_pow]
  ring

theorem finite_geometric_sum_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (K : ℕ) :
    (∑ k ∈ Finset.range K, ρ ^ k) ≤ 1 / (1 - ρ) := by
  have hid : (∑ k ∈ Finset.range K, ρ ^ k) * (1 - ρ) = 1 - ρ ^ K := by
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ, pow_succ]
      nlinarith
  apply (le_div_iff₀ (sub_pos.mpr hρ1)).mpr
  rw [hid]
  exact sub_le_self _ (pow_nonneg hρ0 K)

theorem finite_band_bound {a r χ : ℝ} (ha : 0 < a) (har : a < r) (hχ : 0 ≤ χ)
    (K : ℕ) :
    (∑ k ∈ Finset.range K,
      χ * ((2 ^ (k + 1) : ℕ) : ℝ) ^ (1 / r) * ((1 / 2 : ℝ) ^ k) ^ (1 / a)) ≤
      (χ * (2 : ℝ) ^ (1 / r)) / (1 - bandGeometricRatio a r) := by
  have hterm (k : ℕ) :
      χ * ((2 ^ (k + 1) : ℕ) : ℝ) ^ (1 / r) * ((1 / 2 : ℝ) ^ k) ^ (1 / a) =
      (χ * (2 : ℝ) ^ (1 / r)) * bandGeometricRatio a r ^ k := by
    rw [mul_assoc, band_length_times_size, ← mul_assoc]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have h := mul_le_mul_of_nonneg_left
    (finite_geometric_sum_le (bandGeometricRatio_pos a r).le (bandGeometricRatio_lt_one ha har) K)
    (mul_nonneg hχ (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (1 / r)))
  simpa only [mul_one_div] using h

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteL2
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {Ω E : Type*} [Fintype Ω]
variable [NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]

theorem finiteL2Norm_smul (μ : FiniteLaw Ω) (c : ℝ) (f : Ω → E) :
    finiteL2Norm μ (fun ω => c • f ω) = |c| * finiteL2Norm μ f := by
  apply (sq_eq_sq₀ (finiteL2Norm_nonneg μ _)
    (mul_nonneg (abs_nonneg c) (finiteL2Norm_nonneg μ f))).1
  rw [finiteL2Norm_sq, mul_pow, finiteL2Norm_sq]
  simp only [FiniteLaw.expect]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω hω
  rw [norm_smul, Real.norm_eq_abs, mul_pow]
  ring

@[simp] theorem finiteL2Norm_neg (μ : FiniteLaw Ω) (f : Ω → E) :
    finiteL2Norm μ (fun ω => -f ω) = finiteL2Norm μ f := by
  simpa only [neg_one_smul, abs_neg, abs_one, one_mul] using
    finiteL2Norm_smul μ (-1) f

omit sectionNormedSpaceℝE in
theorem finite_norm_product_le_L2_mul_L2 [NormedSpace ℝ E] (μ : FiniteLaw Ω) (f g : Ω → E) :
    μ.expect (fun ω => ‖f ω‖ * ‖g ω‖) ≤ finiteL2Norm μ f * finiteL2Norm μ g := by
  have h := finite_weighted_holder_univ
    (w := μ.mass) (a := fun ω => ‖f ω‖) (b := fun ω => ‖g ω‖)
    Real.HolderConjugate.two_two μ.mass_nonneg (fun ω => norm_nonneg _)
    (fun ω => norm_nonneg _)
  simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow, finiteL2Norm,
    FiniteLaw.expect, mul_assoc] using h

theorem finiteL2Norm_add_le (μ : FiniteLaw Ω) (f g : Ω → E) :
    finiteL2Norm μ (fun ω => f ω + g ω) ≤ finiteL2Norm μ f + finiteL2Norm μ g := by
  have hcross := finite_norm_product_le_L2_mul_L2 μ f g
  have hexpand : μ.expect (fun ω => (‖f ω‖ + ‖g ω‖) ^ (2 : ℕ)) =
      μ.expect (fun ω => ‖f ω‖ ^ (2 : ℕ)) +
        2 * μ.expect (fun ω => ‖f ω‖ * ‖g ω‖) +
          μ.expect (fun ω => ‖g ω‖ ^ (2 : ℕ)) := by
    simp only [FiniteLaw.expect]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ω hω
    ring
  have hsquare : finiteL2Norm μ (fun ω => f ω + g ω) ^ (2 : ℕ) ≤
      (finiteL2Norm μ f + finiteL2Norm μ g) ^ (2 : ℕ) := by
    calc
      _ = μ.expect (fun ω => ‖f ω + g ω‖ ^ (2 : ℕ)) := finiteL2Norm_sq μ _
      _ ≤ μ.expect (fun ω => (‖f ω‖ + ‖g ω‖) ^ (2 : ℕ)) :=
        μ.expect_mono (fun ω => pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2)
      _ = finiteL2Norm μ f ^ (2 : ℕ) +
          2 * μ.expect (fun ω => ‖f ω‖ * ‖g ω‖) +
            finiteL2Norm μ g ^ (2 : ℕ) := by
        rw [hexpand, finiteL2Norm_sq, finiteL2Norm_sq]
      _ ≤ _ := by nlinarith only [hcross]
  exact (sq_le_sq₀ (finiteL2Norm_nonneg μ _)
    (add_nonneg (finiteL2Norm_nonneg μ f) (finiteL2Norm_nonneg μ g))).1 hsquare

theorem finiteL2Norm_sum_le {ι : Type*} (μ : FiniteLaw Ω)
    (s : Finset ι) (f : ι → Ω → E) :
    finiteL2Norm μ (fun ω => ∑ i ∈ s, f i ω) ≤ ∑ i ∈ s, finiteL2Norm μ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, finiteL2Norm_zero, le_refl]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (finiteL2Norm_add_le μ (f i) (fun ω => ∑ j ∈ s, f j ω)).trans
        (add_le_add_right ih _)

theorem finiteL2Norm_le_of_pointwise (μ : FiniteLaw Ω) (f : Ω → E)
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ ω, ‖f ω‖ ≤ B) : finiteL2Norm μ f ≤ B := by
  apply (sq_le_sq₀ (finiteL2Norm_nonneg μ f) hB).1
  rw [finiteL2Norm_sq]
  calc
    μ.expect (fun ω => ‖f ω‖ ^ (2 : ℕ)) ≤ μ.expect (fun _ => B ^ (2 : ℕ)) :=
      μ.expect_mono (fun ω => pow_le_pow_left₀ (norm_nonneg _) (hf ω) 2)
    _ = B ^ (2 : ℕ) := μ.expect_const _

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteMartingaleTransport
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

universe u v w

namespace MarkovSuperreflexivity

variable {Ω : Type u} {Ξ : Type v} [sectionFintypeΩ : Fintype Ω] [sectionFintypeΞ : Fintype Ξ]

variable {E : Type w} [NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]

theorem HasZeroConditionalSum.reindex {μ : FiniteLaw Ω} {P : Setoid Ω}
    {f : Ω → E} (hf : HasZeroConditionalSum μ P f) (e : Ξ ≃ Ω) :
    HasZeroConditionalSum (μ.reindex e) (Setoid.comap e P) (f ∘ e) := by
  classical
  intro a
  change (∑ ξ, if P.r (e ξ) (e a) then μ.mass (e ξ) • f (e ξ) else 0) = 0
  exact (e.sum_comp (fun ω => if P.r ω (e a) then μ.mass ω • f ω else 0)).trans
    (hf (e a))

namespace FinitePartitionFiltration

theorem IsMartingaleUpTo.reindex {F : FinitePartitionFiltration Ω}
    {μ : FiniteLaw Ω} {M : ℕ → Ω → E} {N : ℕ}
    (hM : F.IsMartingaleUpTo μ M N) (e : Ξ ≃ Ω) :
    (F.reindex e).IsMartingaleUpTo (μ.reindex e) (fun n => M n ∘ e) N := by
  constructor
  · intro n hn ξ η hξη
    exact hM.1 n hn hξη
  · intro n hn hnN
    rw [finiteDifference_comp_equiv]
    exact (hM.2 n hn hnN).reindex e

end FinitePartitionFiltration

theorem FiniteUpperL2.apply {r χ : ℝ} (h : FiniteUpperL2 E r χ)
    (μ : FiniteLaw Ω) (F : FinitePartitionFiltration Ω) (M : ℕ → Ω → E)
    (N : ℕ) (B : ℝ) (hB : 0 ≤ B) (hM : F.IsMartingaleUpTo μ M N)
    (hd : ∀ j : ℕ, j ≤ N → finiteL2Norm μ (finiteDifference M j) ≤ B) :
    finiteL2Norm μ (M N) ≤ χ * (N + 1 : ℝ) ^ (1 / r) * B := by
  let e : Fin (Fintype.card Ω) ≃ Ω := (Fintype.equivFin Ω).symm
  have hd' : ∀ j : ℕ, j ≤ N →
      finiteL2Norm (μ.reindex e) (finiteDifference (fun n => M n ∘ e) j) ≤ B := by
    intro j hj
    simpa only [finiteDifference_comp_equiv, finiteL2Norm_reindex] using hd j hj
  have hbound := h (Fintype.card Ω) (μ.reindex e) (F.reindex e)
    (fun n => M n ∘ e) N B hB (hM.reindex e) hd'
  simpa only [finiteL2Norm_reindex] using hbound

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FinitePredictableSelection
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

variable {Ω E : Type*} [sectionFintypeΩ : Fintype Ω]
variable [NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]

omit sectionFintypeΩ sectionNormedSpaceℝE in
theorem finiteSelectedValue_eq_sum [Fintype Ω] [NormedSpace ℝ E] (N : ℕ) (d : ℕ → Ω → E) (σ : Ω → ℕ)
    (hpos : ∀ ω, 0 < σ ω) (ω : Ω) :
    finiteSelectedValue N d σ ω =
      ∑ n ∈ Finset.Icc 1 N, if σ ω = n then d n ω else 0 := by
  classical
  by_cases hle : σ ω ≤ N
  · have hmem : σ ω ∈ Finset.Icc 1 N :=
      Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt (hpos ω), hle⟩
    rw [finiteSelectedValue, ite_eq_left hle]
    symm
    rw [Finset.sum_eq_single (σ ω)]
    · simp
    · intro n _ hne
      simp only [ite_eq_right (Ne.symm hne)]
    · intro hnot
      exact (hnot hmem).elim
  · rw [finiteSelectedValue, ite_eq_right hle]
    symm
    apply Finset.sum_eq_zero
    intro n hn
    have hne : σ ω ≠ n := by
      intro heq
      exact hle (heq.symm ▸ (Finset.mem_Icc.mp hn).2)
    simp only [ite_eq_right hne]

theorem HasZeroConditionalSum.vexpect_eq_zero {μ : FiniteLaw Ω} {P : Setoid Ω}
    {f : Ω → E} (hf : HasZeroConditionalSum μ P f) : μ.vexpect f = 0 := by
  classical
  let : Fintype (Quotient P) := Quotient.fintype P
  let key : Ω → Quotient P := Quotient.mk P
  have hzero : ∀ a : Quotient P, μ.fiberSum key f a = 0 := by
    intro a
    refine Quotient.inductionOn a ?_
    intro b
    simpa only [FiniteLaw.fiberSum, FiniteLaw.fiberWeight, key, Quotient.eq,
      ite_smul, zero_smul] using hf b
  simpa only [one_smul] using μ.vexpect_key_smul_eq_zero key f hzero (fun _ => 1)

namespace FinitePartitionFiltration

theorem finiteSelectedValue_zero_conditionalSum (F : FinitePartitionFiltration Ω)
    (μ : FiniteLaw Ω) (N : ℕ) (d : ℕ → Ω → E) (τ σ : Ω → ℕ)
    (hτ : F.IsStoppingTime τ) (hσ : F.IsPredictableTime σ)
    (hpos : ∀ ω, 0 < σ ω)
    (hstrict : ∀ ω, σ ω ≤ N → τ ω < σ ω)
    (hzero : ∀ n : ℕ, 0 < n → n ≤ N →
      HasZeroConditionalSum μ (F.part (n - 1)) (d n)) :
    HasZeroConditionalSum μ (F.stoppedSetoid τ) (finiteSelectedValue N d σ) := by
  classical
  intro a
  calc
    (∑ ω, if (F.stoppedSetoid τ).r ω a then
        μ.mass ω • finiteSelectedValue N d σ ω else 0) =
        ∑ ω, ∑ n ∈ Finset.Icc 1 N,
          if (F.stoppedSetoid τ).r ω a ∧ σ ω = n then μ.mass ω • d n ω else 0 := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [finiteSelectedValue_eq_sum N d σ hpos ω]
      by_cases ha : (F.stoppedSetoid τ).r ω a
      · simp only [ha, ite_true, true_and, Finset.smul_sum, smul_ite, smul_zero]
      · simp only [ha, false_and, ite_false, Finset.sum_const_zero]
    _ = ∑ n ∈ Finset.Icc 1 N,
        μ.vexpect (fun ω =>
          if (F.stoppedSetoid τ).r ω a ∧ σ ω = n then d n ω else 0) := by
      rw [Finset.sum_comm]
      simp only [FiniteLaw.vexpect, smul_ite, smul_zero]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
      have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
      have hbefore : ∀ ω, σ ω = n → τ ω < n := by
        intro ω heq
        have hle : σ ω ≤ N := by simpa only [heq] using hnN
        simpa only [heq] using hstrict ω hle
      have hcancel := (hzero n hnpos hnN).indicator
        (fun ω => (F.stoppedSetoid τ).r ω a ∧ σ ω = n) (by
          intro ω η hωη
          exact F.stopped_atom_and_predictable_eq hτ hσ a hnpos hbefore hωη)
      have hdec :
          (fun ω => if (F.stoppedSetoid τ).r ω a ∧ σ ω = n then d n ω else 0) =
          (fun ω => @ite E ((F.stoppedSetoid τ).r ω a ∧ σ ω = n)
            (Classical.propDecidable _) (d n ω) 0) := by
        funext ω
        by_cases h : (F.stoppedSetoid τ).r ω a ∧ σ ω = n
        · simp only [ite_eq_left h]
        · simp only [ite_eq_right h]
      rw [hdec]
      exact hcancel.vexpect_eq_zero

omit sectionFintypeΩ sectionNormedSpaceℝE in
theorem finiteSelectedValue_adapted_stopped [Fintype Ω] [NormedSpace ℝ E] (F : FinitePartitionFiltration Ω)
    (N : ℕ) (d : ℕ → Ω → E) (σ : Ω → ℕ)
    (hpos : ∀ ω, 0 < σ ω)
    (hadapt : ∀ n : ℕ, 0 < n → n ≤ N → F.AdaptedAt n (d n))
    {ω η : Ω} (hωη : (F.stoppedSetoid σ).r ω η) :
    finiteSelectedValue N d σ ω = finiteSelectedValue N d σ η := by
  by_cases hle : σ ω ≤ N
  · have hleη : σ η ≤ N := hωη.1 ▸ hle
    simp only [finiteSelectedValue, ite_eq_left hle, ite_eq_left hleη]
    rw [← hωη.1]
    exact hadapt (σ ω) (hpos ω) hle hωη.2
  · have hleη : ¬σ η ≤ N := by simpa only [← hωη.1] using hle
    simp only [finiteSelectedValue, ite_eq_right hle, ite_eq_right hleη]

end FinitePartitionFiltration

namespace FinitePartitionFiltration

theorem finiteSelectedProcess_adapted (F : FinitePartitionFiltration Ω)
    (N : ℕ) (d : ℕ → Ω → E) (τ : ℕ → Ω → ℕ)
    (hstop : ∀ i, F.IsStoppingTime (τ i))
    (hmono : ∀ ω, Monotone (fun i => τ i ω))
    (hpos : ∀ i ω, 0 < τ (i + 1) ω)
    (hadapt : ∀ n : ℕ, 0 < n → n ≤ N → F.AdaptedAt n (d n)) (j : ℕ) :
    (F.selectedFiltration τ hstop hmono).AdaptedAt j (finiteSelectedProcess N d τ j) := by
  intro ω η hωη
  apply Finset.sum_congr rfl
  intro i hi
  have hij : i + 1 ≤ j := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
  have hrel : (F.stoppedSetoid (τ (i + 1))).r ω η :=
    F.stoppedSetoid_refines (hstop (i + 1)) (fun ν => hmono ν hij) hωη
  exact F.finiteSelectedValue_adapted_stopped N d (τ (i + 1)) (hpos i) hadapt hrel

theorem finiteSelectedProcess_isMartingaleUpTo (F : FinitePartitionFiltration Ω)
    (μ : FiniteLaw Ω) (N : ℕ) (d : ℕ → Ω → E) (τ : ℕ → Ω → ℕ)
    (hstop : ∀ i, F.IsStoppingTime (τ i))
    (hmono : ∀ ω, Monotone (fun i => τ i ω))
    (hpred : ∀ i, F.IsPredictableTime (τ (i + 1)))
    (hpos : ∀ i ω, 0 < τ (i + 1) ω)
    (hstrict : ∀ i ω, τ (i + 1) ω ≤ N → τ i ω < τ (i + 1) ω)
    (hadapt : ∀ n : ℕ, 0 < n → n ≤ N → F.AdaptedAt n (d n))
    (hzero : ∀ n : ℕ, 0 < n → n ≤ N →
      HasZeroConditionalSum μ (F.part (n - 1)) (d n)) (J : ℕ) :
    (F.selectedFiltration τ hstop hmono).IsMartingaleUpTo μ
      (finiteSelectedProcess N d τ) J := by
  constructor
  · intro j _
    exact F.finiteSelectedProcess_adapted N d τ hstop hmono hpos hadapt j
  · intro j hj _
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
    have hdiff : finiteDifference (finiteSelectedProcess N d τ) (i + 1) =
        finiteSelectedValue N d (τ (i + 1)) :=
      funext (finiteDifference_selectedProcess_succ N d τ i)
    change HasZeroConditionalSum μ (F.stoppedSetoid (τ ((i + 1) - 1)))
      (finiteDifference (finiteSelectedProcess N d τ) (i + 1))
    rw [Nat.add_sub_cancel, hdiff]
    exact F.finiteSelectedValue_zero_conditionalSum μ N d (τ i) (τ (i + 1))
      (hstop i) (hpred i) (hpos i) (hstrict i) hzero

end FinitePartitionFiltration

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteSelectionCounter
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

variable {Ω : Type*}

theorem selectionSlot_strict_before_horizon {N i j : ℕ} (B : ℕ → Ω → Prop)
    (ω : Ω) (hij : i < j) (hj : selectionSlot N B j ω ≤ N) :
    selectionSlot N B i ω < selectionSlot N B j ω := by
  have hj' := (selectionSlot_le_horizon_iff N j B ω).mp hj
  have hi := hij.trans hj'
  simp only [selectionSlot, ite_eq_left hi, ite_eq_left hj']
  exact Nat.nth_lt_nth' hij (fun hf => hj'.trans_le (Nat.count_le_card hf (N + 1)))

theorem selectionTime_strict_before_horizon {N i : ℕ} (B : ℕ → Ω → Prop)
    (ω : Ω) (hi : selectionTime N B (i + 1) ω ≤ N) :
    selectionTime N B i ω < selectionTime N B (i + 1) ω := by
  cases i with
  | zero => exact selectionSlot_pos N 0 B ω
  | succ i => exact selectionSlot_strict_before_horizon B ω (Nat.lt_succ_self i) hi

theorem sum_selectionSlot {V : Type*} [AddCommMonoid V]
    (N : ℕ) (B : ℕ → Ω → Prop) (ω : Ω) (f : ℕ → V) :
    (∑ i ∈ Finset.range (selectionCount N B ω), f (selectionSlot N B i ω)) =
      ∑ n ∈ (Finset.range (N + 1)).filter (selectionPredicate N B ω), f n := by
  apply Finset.sum_bij (fun i _ => selectionSlot N B i ω)
  · intro i hi
    have hmem := selectionSlot_mem (Finset.mem_range.mp hi)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hmem.2.1), hmem⟩
  · intro i hi j hj hij
    have hirank := selectionSlot_rank (Finset.mem_range.mp hi)
    have hjrank := selectionSlot_rank (Finset.mem_range.mp hj)
    rw [hij] at hirank
    exact hirank.symm.trans hjrank
  · intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnrange, hnP⟩
    refine ⟨Nat.count (selectionPredicate N B ω) n, ?_, ?_⟩
    · exact Finset.mem_range.mpr
        (Nat.count_strict_mono hnP (Finset.mem_range.mp hnrange))
    · exact (selectionSlot_eq_iff B ω hnP.2.1).mpr ⟨hnP, rfl⟩
  · intro i hi
    rfl

theorem sum_selectionSlot_padded {V : Type*} [AddCommMonoid V]
    (N : ℕ) (B : ℕ → Ω → Prop) (ω : Ω) (f : ℕ → V) (J : ℕ)
    (hJ : selectionCount N B ω ≤ J) :
    (∑ i ∈ Finset.range J,
      if selectionSlot N B i ω ≤ N then f (selectionSlot N B i ω) else 0) =
      ∑ n ∈ Finset.range (N + 1), if selectionPredicate N B ω n then f n else 0 := by
  calc
    _ = ∑ i ∈ Finset.range (selectionCount N B ω),
        if selectionSlot N B i ω ≤ N then f (selectionSlot N B i ω) else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono hJ)
      intro i hi hin
      have hnot : ¬i < selectionCount N B ω := fun h => hin (Finset.mem_range.mpr h)
      have hnotN : ¬selectionSlot N B i ω ≤ N :=
        fun h => hnot ((selectionSlot_le_horizon_iff N i B ω).mp h)
      exact ite_eq_right hnotN
    _ = ∑ i ∈ Finset.range (selectionCount N B ω), f (selectionSlot N B i ω) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact ite_eq_left (selectionSlot_mem (Finset.mem_range.mp hi)).2.1
    _ = ∑ n ∈ (Finset.range (N + 1)).filter (selectionPredicate N B ω), f n :=
      sum_selectionSlot N B ω f
    _ = _ := by rw [Finset.sum_filter]

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteSelectionCompression
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

variable {Ω E : Type*} [sectionFintypeΩ : Fintype Ω]
variable [NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]

omit sectionFintypeΩ sectionNormedSpaceℝE in
theorem selectionProcess_eq_sum [Fintype Ω] [NormedSpace ℝ E] (N : ℕ) (B : ℕ → Ω → Prop)
    (d : ℕ → Ω → E) (J : ℕ) (ω : Ω) (hJ : selectionCount N B ω ≤ J) :
    selectionProcess N B d J ω =
      ∑ n ∈ Finset.Icc 1 N, if B n ω then d n ω else 0 := by
  classical
  calc
    _ = ∑ n ∈ Finset.range (N + 1),
        if selectionPredicate N B ω n then d n ω else 0 :=
      sum_selectionSlot_padded N B ω (fun n => d n ω) J hJ
    _ = ∑ n ∈ Finset.Icc 1 N,
        if selectionPredicate N B ω n then d n ω else 0 := by
      symm
      apply Finset.sum_subset
      · intro n hn
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hn).2)
      · intro n hn hnot
        have hnN : n ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
        have hnzero : n = 0 := by
          by_contra hne
          exact hnot (Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hne, hnN⟩)
        simp only [selectionPredicate, hnzero, Nat.lt_irrefl, false_and, ite_false]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
      have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
      simp only [selectionPredicate, hnpos, hnN, true_and]

theorem norm_finiteDifference_selectionProcess_le (N : ℕ) (B : ℕ → Ω → Prop)
    (d : ℕ → Ω → E) {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ n, 0 < n → n ≤ N → ∀ ω, B n ω → ‖d n ω‖ ≤ C)
    (i : ℕ) (ω : Ω) :
    ‖finiteDifference (selectionProcess N B d) (i + 1) ω‖ ≤ C := by
  rw [finiteDifference_selectionProcess_succ]
  by_cases hle : selectionSlot N B i ω ≤ N
  · rw [ite_eq_left hle]
    have hmem := selectionSlot_mem ((selectionSlot_le_horizon_iff N i B ω).mp hle)
    exact hd (selectionSlot N B i ω) hmem.1 hmem.2.1 ω hmem.2.2
  · simpa only [ite_eq_right hle, norm_zero] using hC

namespace FinitePartitionFiltration

theorem selectionProcess_isMartingaleUpTo (F : FinitePartitionFiltration Ω)
    (μ : FiniteLaw Ω) (N : ℕ) (B : ℕ → Ω → Prop) (d : ℕ → Ω → E)
    (hB : ∀ n, 0 < n → n ≤ N → ∀ {ω η},
      (F.part (n - 1)).r ω η → (B n ω ↔ B n η))
    (hadapt : ∀ n, 0 < n → n ≤ N → F.AdaptedAt n (d n))
    (hzero : ∀ n, 0 < n → n ≤ N →
      HasZeroConditionalSum μ (F.part (n - 1)) (d n)) (J : ℕ) :
    (F.selectionFiltration N B hB).IsMartingaleUpTo μ (selectionProcess N B d) J := by
  exact F.finiteSelectedProcess_isMartingaleUpTo μ N d (selectionTime N B)
    (selectionTime_stopping F N B hB) (selectionTime_monotone N B)
    (selectionSlot_predictable F N B hB) (fun i => selectionSlot_pos N i B)
    (fun i ω hi => selectionTime_strict_before_horizon B ω hi) hadapt hzero J

end FinitePartitionFiltration

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteBoundedEnergy
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

variable {Ω E : Type*} [sectionFintypeΩ : Fintype Ω]
variable [NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]

theorem sum_Icc_one_eq_sum_range_succ {V : Type*} [AddCommMonoid V]
    (f : ℕ → V) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, f n) = ∑ j ∈ Finset.range N, f (j + 1) := by
  rw [← Finset.Ico_succ_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.succ_eq_succ, Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.add_comm 1]

omit sectionFintypeΩ in
theorem selectionCount_eq_card_filter_Icc [Fintype Ω] (N : ℕ) (B : ℕ → Ω → Prop) (ω : Ω) :
    selectionCount N B ω = ((Finset.Icc 1 N).filter (fun n => B n ω)).card := by
  have hcount : selectionCount N B ω =
      ((Finset.range (N + 1)).filter (selectionPredicate N B ω)).card := by
    exact Nat.count_eq_card_filter_range (selectionPredicate N B ω) (N + 1)
  have hsets : (Finset.range (N + 1)).filter (selectionPredicate N B ω) =
      (Finset.Icc 1 N).filter (fun n => B n ω) := by
    apply Finset.ext
    intro n
    constructor
    · intro hn
      have hselect : selectionPredicate N B ω n := (Finset.mem_filter.mp hn).2
      change 0 < n ∧ n ≤ N ∧ B n ω at hselect
      rcases hselect with ⟨hpos, hN, hB⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hN⟩, hB⟩
    · intro hn
      obtain ⟨hnIcc, hB⟩ := Finset.mem_filter.mp hn
      obtain ⟨hpos, hN⟩ := Finset.mem_Icc.mp hnIcc
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hN), ?_⟩
      change 0 < n ∧ n ≤ N ∧ B n ω
      exact ⟨by omega, hN, hB⟩
  exact hcount.trans (congrArg Finset.card hsets)

theorem finiteUpperL2_band_bound {a r χ : ℝ} (ha : 0 < a)
    (hUpper : FiniteUpperL2 E r χ) (μ : FiniteLaw Ω)
    (F : FinitePartitionFiltration Ω) (d : ℕ → Ω → E) (N k : ℕ)
    (hadapt : ∀ n, 0 < n → n ≤ N → F.AdaptedAt n (d n))
    (hzero : ∀ n, 0 < n → n ≤ N → HasZeroConditionalSum μ (F.part (n - 1)) (d n))
    (hpred : ∀ n, 0 < n → n ≤ N → F.AdaptedAt (n - 1) (fun ω => ‖d n ω‖))
    (henergy : ∀ ω, (∑ n ∈ Finset.Icc 1 N, ‖d n ω‖ ^ a) ≤ 1) :
    finiteL2Norm μ (fun ω => ∑ n ∈ Finset.Icc 1 N,
      if dyadicMagnitudeBand k (‖d n ω‖ ^ a) then d n ω else 0) ≤
      χ * ((2 ^ (k + 1) : ℕ) : ℝ) ^ (1 / r) * ((1 / 2 : ℝ) ^ k) ^ (1 / a) := by
  let B : ℕ → Ω → Prop := fun n ω => dyadicMagnitudeBand k (‖d n ω‖ ^ a)
  let J : ℕ := 2 ^ (k + 1) - 1
  have hB : ∀ n, 0 < n → n ≤ N → ∀ {ω η},
      (F.part (n - 1)).r ω η → (B n ω ↔ B n η) := by
    intro n hn hnN ω η hωη
    dsimp only [B]
    have hnorm : ‖d n ω‖ = ‖d n η‖ := hpred n hn hnN hωη
    rw [hnorm]
  have hcount (ω : Ω) : selectionCount N B ω ≤ J := by
    rw [selectionCount_eq_card_filter_Icc]
    have hc := dyadicMagnitudeBand_card_lt (Finset.Icc 1 N) (fun n => ‖d n ω‖ ^ a)
      (fun n _ => Real.rpow_nonneg (norm_nonneg _) a) (henergy ω) k
    change ((Finset.Icc 1 N).filter (fun n => dyadicMagnitudeBand k (‖d n ω‖ ^ a))).card
      ≤ 2 ^ (k + 1) - 1
    omega
  have hC : 0 ≤ ((1 / 2 : ℝ) ^ k) ^ (1 / a) :=
    Real.rpow_nonneg (pow_nonneg (by norm_num) k) _
  have hM := F.selectionProcess_isMartingaleUpTo μ N B d hB hadapt hzero J
  have hd : ∀ j, j ≤ J →
      finiteL2Norm μ (finiteDifference (selectionProcess N B d) j) ≤
        ((1 / 2 : ℝ) ^ k) ^ (1 / a) := by
    intro j hj
    apply finiteL2Norm_le_of_pointwise μ _ hC
    intro ω
    cases j with
    | zero => simpa only [finiteDifference_zero, selectionProcess_zero, norm_zero] using hC
    | succ j =>
      exact norm_finiteDifference_selectionProcess_le N B d hC
        (fun n hn hnN η hnB => norm_le_band_bound ha hnB) j ω
  have h := hUpper.apply μ (F.selectionFiltration N B hB)
    (selectionProcess N B d) J (((1 / 2 : ℝ) ^ k) ^ (1 / a)) hC hM hd
  have hterminal : selectionProcess N B d J = fun ω => ∑ n ∈ Finset.Icc 1 N,
      if dyadicMagnitudeBand k (‖d n ω‖ ^ a) then d n ω else 0 := by
    funext ω
    exact selectionProcess_eq_sum N B d J ω (hcount ω)
  have hJ : J + 1 = 2 ^ (k + 1) := by
    have hp : 0 < 2 ^ (k + 1) := pow_pos (by decide : (0 : ℕ) < 2) _
    dsimp only [J]
    omega
  rw [hterminal] at h
  have hJreal : (J + 1 : ℝ) = ((2 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast hJ
  rwa [hJreal] at h

theorem boundedEnergyConstant_nonneg {a r χ : ℝ}
    (ha : 0 < a) (har : a < r) (hχ : 0 ≤ χ) :
    0 ≤ boundedEnergyConstant a r χ :=
  div_nonneg (mul_nonneg hχ (Real.rpow_nonneg (by norm_num) _))
    (sub_nonneg.mpr (bandGeometricRatio_lt_one ha har).le)

omit sectionNormedSpaceℝE in
theorem finite_band_decomposition [NormedSpace ℝ E] {a : ℝ} (_ha : 0 < a)
    (d : ℕ → Ω → E) (N : ℕ)
    (henergy : ∀ ω, (∑ n ∈ Finset.Icc 1 N, ‖d n ω‖ ^ a) ≤ 1) :
    ∃ K : ℕ, ∀ ω,
      (∑ n ∈ Finset.Icc 1 N, d n ω) =
        ∑ k ∈ Finset.range (K + 1), ∑ n ∈ Finset.Icc 1 N,
          if dyadicMagnitudeBand k (‖d n ω‖ ^ a) then d n ω else 0 := by
  classical
  let w : (Ω × ↥(Finset.Icc 1 N)) → ℝ := fun z => ‖d z.2.val z.1‖ ^ a
  have hw : ∀ z, w z ≤ 1 := by
    intro z
    exact (Finset.single_le_sum
      (fun n _ => Real.rpow_nonneg (norm_nonneg (d n z.1)) a) z.2.property).trans (henergy z.1)
  obtain ⟨K, hK⟩ := finite_dyadicMagnitudeBand_cutoff w hw
  refine ⟨K, ?_⟩
  intro ω
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hd : d n ω = 0
  · simp only [hd, ite_self, Finset.sum_const_zero]
  · have hwpos : 0 < w (ω, ⟨n, hn⟩) :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr hd) a
    obtain ⟨k, hkK, hband⟩ := hK (ω, ⟨n, hn⟩) hwpos
    have hk : k ∈ Finset.range (K + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hkK)
    change dyadicMagnitudeBand k (‖d n ω‖ ^ a) at hband
    symm
    calc
      _ = if dyadicMagnitudeBand k (‖d n ω‖ ^ a) then d n ω else 0 := by
        apply Finset.sum_eq_single k
        · intro l hl hlk
          apply ite_eq_right
          intro hlband
          exact hlk (dyadicMagnitudeBand_unique hlband hband)
        · intro hnot
          exact (hnot hk).elim
      _ = d n ω := ite_eq_left hband

theorem finiteUpperL2_bounded_energy {a r χ : ℝ} (ha : 0 < a) (har : a < r)
    (hχ : 0 ≤ χ) (hUpper : FiniteUpperL2 E r χ) (μ : FiniteLaw Ω)
    (F : FinitePartitionFiltration Ω) (d : ℕ → Ω → E) (N : ℕ)
    (hadapt : ∀ n, 0 < n → n ≤ N → F.AdaptedAt n (d n))
    (hzero : ∀ n, 0 < n → n ≤ N → HasZeroConditionalSum μ (F.part (n - 1)) (d n))
    (hpred : ∀ n, 0 < n → n ≤ N → F.AdaptedAt (n - 1) (fun ω => ‖d n ω‖))
    (henergy : ∀ ω, (∑ n ∈ Finset.Icc 1 N, ‖d n ω‖ ^ a) ≤ 1) :
    finiteL2Norm μ (fun ω => ∑ n ∈ Finset.Icc 1 N, d n ω) ≤
      boundedEnergyConstant a r χ := by
  obtain ⟨K, hK⟩ := finite_band_decomposition ha d N henergy
  have heq : (fun ω => ∑ n ∈ Finset.Icc 1 N, d n ω) =
      fun ω => ∑ k ∈ Finset.range (K + 1), ∑ n ∈ Finset.Icc 1 N,
        if dyadicMagnitudeBand k (‖d n ω‖ ^ a) then d n ω else 0 := funext hK
  rw [heq]
  calc
    _ ≤ ∑ k ∈ Finset.range (K + 1),
        finiteL2Norm μ (fun ω => ∑ n ∈ Finset.Icc 1 N,
          if dyadicMagnitudeBand k (‖d n ω‖ ^ a) then d n ω else 0) :=
      finiteL2Norm_sum_le μ _ _
    _ ≤ ∑ k ∈ Finset.range (K + 1),
        χ * ((2 ^ (k + 1) : ℕ) : ℝ) ^ (1 / r) * ((1 / 2 : ℝ) ^ k) ^ (1 / a) := by
      apply Finset.sum_le_sum
      intro k hk
      exact finiteUpperL2_band_bound ha hUpper μ F d N k hadapt hzero hpred henergy
    _ ≤ boundedEnergyConstant a r χ := finite_band_bound ha har hχ (K + 1)

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FinitePredictableTransform
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

variable {Ω E : Type*} [sectionFintypeΩ : Fintype Ω]
variable [NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]

theorem partialSumProcess_isMartingale (F : FinitePartitionFiltration Ω)
    (μ : FiniteLaw Ω) (d : ℕ → Ω → E) (N : ℕ)
    (hadapt : ∀ j, 0 < j → j ≤ N → F.AdaptedAt j (d j))
    (hzero : ∀ j, 0 < j → j ≤ N →
      HasZeroConditionalSum μ (F.part (j - 1)) (d j)) :
    F.IsMartingaleUpTo μ (partialSumProcess d) N := by
  constructor
  · intro n hn ω η hωη
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j + 1 ≤ n := Nat.succ_le_of_lt (Finset.mem_range.mp hj)
    exact hadapt (j + 1) (Nat.succ_pos j) (hjn.trans hn) (F.refines hjn hωη)
  · intro j hj hjN
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
    have hd : finiteDifference (partialSumProcess d) (n + 1) = d (n + 1) :=
      funext (difference_partialSumProcess_succ d n)
    rw [hd]
    exact hzero (n + 1) (Nat.succ_pos n) hjN

theorem predictableTransform_isMartingale (F : FinitePartitionFiltration Ω)
    (μ : FiniteLaw Ω) (d : ℕ → Ω → E) (c : ℕ → Ω → ℝ) (N : ℕ)
    (hadapt : ∀ j, 0 < j → j ≤ N → F.AdaptedAt j (d j))
    (hzero : ∀ j, 0 < j → j ≤ N →
      HasZeroConditionalSum μ (F.part (j - 1)) (d j))
    (hc : ∀ j, 0 < j → j ≤ N → F.AdaptedAt (j - 1) (c j)) :
    F.IsMartingaleUpTo μ (partialSumProcess (fun j ω => c j ω • d j ω)) N := by
  apply partialSumProcess_isMartingale F μ _ N
  · intro j hj hjN ω η hωη
    dsimp only
    rw [hc j hj hjN (F.refines (Nat.sub_le j 1) hωη),
      hadapt j hj hjN hωη]
  · intro j hj hjN
    exact (hzero j hj hjN).predictable_smul (c j) (hc j hj hjN)

omit sectionFintypeΩ in
theorem cumulativeCost_succ [Fintype Ω] (w : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    cumulativeCost w (n + 1) ω = cumulativeCost w n ω + w (n + 1) ω := by
  exact Finset.sum_range_succ _ _

theorem cumulativeCost_mono (w : ℕ → Ω → ℝ)
    (hw : ∀ j ω, 0 ≤ w j ω) (ω : Ω) :
    Monotone (fun n => cumulativeCost w n ω) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [cumulativeCost_succ]
  exact le_add_of_nonneg_right (hw (n + 1) ω)

omit sectionFintypeΩ in
theorem cumulativeCost_predictable [Fintype Ω] (F : FinitePartitionFiltration Ω)
    (w : ℕ → Ω → ℝ) (N : ℕ)
    (hw : ∀ j, 0 < j → j ≤ N → F.AdaptedAt (j - 1) (w j))
    {n : ℕ} (hn : n ≤ N) :
    F.AdaptedAt (n - 1) (cumulativeCost w n) := by
  intro ω η hωη
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j + 1 ≤ n := Nat.succ_le_of_lt (Finset.mem_range.mp hj)
  have hpart : j + 1 - 1 ≤ n - 1 := Nat.sub_le_sub_right hjn 1
  exact hw (j + 1) (Nat.succ_pos j) (hjn.trans hn) (F.refines hpart hωη)

theorem budgetCoefficient_predictable (F : FinitePartitionFiltration Ω)
    (w : ℕ → Ω → ℝ) (N : ℕ) (S : ℝ)
    (hw : ∀ j, 0 < j → j ≤ N → F.AdaptedAt (j - 1) (w j))
    {n : ℕ} (hn : n ≤ N) :
    F.AdaptedAt (n - 1) (budgetCoefficient w S n) := by
  intro ω η hωη
  unfold budgetCoefficient
  rw [cumulativeCost_predictable F w N hw hn hωη]

theorem budgetTransform_isMartingale (F : FinitePartitionFiltration Ω)
    (μ : FiniteLaw Ω) (d : ℕ → Ω → E) (w : ℕ → Ω → ℝ) (N : ℕ) (S : ℝ)
    (hadapt : ∀ j, 0 < j → j ≤ N → F.AdaptedAt j (d j))
    (hzero : ∀ j, 0 < j → j ≤ N →
      HasZeroConditionalSum μ (F.part (j - 1)) (d j))
    (hw : ∀ j, 0 < j → j ≤ N → F.AdaptedAt (j - 1) (w j)) :
    F.IsMartingaleUpTo μ
      (partialSumProcess (fun j ω => budgetCoefficient w S j ω • d j ω)) N := by
  apply predictableTransform_isMartingale F μ d (budgetCoefficient w S) N hadapt hzero
  intro j hj hjN
  exact budgetCoefficient_predictable F w N S hw hjN

theorem budgetCoefficient_eq_one_of_cost_le (w : ℕ → Ω → ℝ)
    (hw : ∀ j ω, 0 ≤ w j ω) {S : ℝ} {n j : ℕ} {ω : Ω}
    (hj : j ≤ n) (hcost : cumulativeCost w n ω ≤ S) :
    budgetCoefficient w S j ω = 1 := by
  apply ite_eq_left
  exact (cumulativeCost_mono w hw ω hj).trans hcost

theorem budgetTransform_eq_of_cost_le (d : ℕ → Ω → E) (w : ℕ → Ω → ℝ)
    (hw : ∀ j ω, 0 ≤ w j ω) {S : ℝ} {N n : ℕ} {ω : Ω}
    (hn : n ≤ N) (hcost : cumulativeCost w N ω ≤ S) :
    partialSumProcess (fun j η => budgetCoefficient w S j η • d j η) n ω =
      partialSumProcess d n ω := by
  apply Finset.sum_congr rfl
  intro j hj
  have hjN : j + 1 ≤ N := (Nat.succ_le_of_lt (Finset.mem_range.mp hj)).trans hn
  dsimp only
  rw [budgetCoefficient_eq_one_of_cost_le w hw hjN hcost, one_smul]

theorem retainedCost_eq_of_cost_le (w : ℕ → Ω → ℝ)
    (hw : ∀ j ω, 0 ≤ w j ω) {S : ℝ} {n : ℕ} {ω : Ω}
    (hcost : cumulativeCost w n ω ≤ S) :
    cumulativeCost (fun j η => budgetCoefficient w S j η * w j η) n ω =
      cumulativeCost w n ω := by
  apply Finset.sum_congr rfl
  intro j hj
  dsimp only
  rw [budgetCoefficient_eq_one_of_cost_le w hw
    (Nat.succ_le_of_lt (Finset.mem_range.mp hj)) hcost, one_mul]

theorem retainedCost_le (w : ℕ → Ω → ℝ) (hw : ∀ j ω, 0 ≤ w j ω)
    {S : ℝ} (hS : 0 ≤ S) (n : ℕ) (ω : Ω) :
    cumulativeCost (fun j η => budgetCoefficient w S j η * w j η) n ω ≤ S := by
  induction n with
  | zero => simpa only [cumulativeCost_zero] using hS
  | succ n ih =>
    by_cases hcost : cumulativeCost w (n + 1) ω ≤ S
    · rw [retainedCost_eq_of_cost_le w hw hcost]
      exact hcost
    · rw [cumulativeCost_succ]
      simp only [budgetCoefficient, ite_eq_right hcost, zero_mul, add_zero]
      exact ih

theorem budgetTransform_energy_le (d : ℕ → Ω → E) {p S : ℝ}
    (hp : 0 < p) (hS : 0 ≤ S) (n : ℕ) (ω : Ω) :
    (∑ j ∈ Finset.range n,
      ‖budgetCoefficient (fun k η => ‖d k η‖ ^ p) S (j + 1) ω • d (j + 1) ω‖ ^ p)
      ≤ S := by
  have heq : (∑ j ∈ Finset.range n,
      ‖budgetCoefficient (fun k η => ‖d k η‖ ^ p) S (j + 1) ω • d (j + 1) ω‖ ^ p) =
      cumulativeCost (fun j η =>
        budgetCoefficient (fun k ξ => ‖d k ξ‖ ^ p) S j η * ‖d j η‖ ^ p) n ω := by
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only
    unfold budgetCoefficient
    split_ifs with h <;> simp [ Real.zero_rpow (ne_of_gt hp)]
  rw [heq]
  exact retainedCost_le (fun j η => ‖d j η‖ ^ p)
    (fun j η => Real.rpow_nonneg (norm_nonneg _) _) hS n ω

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteBoundedEnergyScale
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {Ω E : Type*} [Fintype Ω]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finiteUpperL2_bounded_energy_scale {a r χ s : ℝ}
    (ha : 0 < a) (har : a < r) (hχ : 0 ≤ χ) (hs : 0 < s)
    (hUpper : FiniteUpperL2 E r χ) (μ : FiniteLaw Ω)
    (F : FinitePartitionFiltration Ω) (d : ℕ → Ω → E) (N : ℕ)
    (hadapt : ∀ n, 0 < n → n ≤ N → F.AdaptedAt n (d n))
    (hzero : ∀ n, 0 < n → n ≤ N → HasZeroConditionalSum μ (F.part (n - 1)) (d n))
    (hpred : ∀ n, 0 < n → n ≤ N → F.AdaptedAt (n - 1) (fun ω => ‖d n ω‖))
    (henergy : ∀ ω, (∑ n ∈ Finset.Icc 1 N, ‖d n ω‖ ^ a) ≤ s ^ a) :
    finiteL2Norm μ (fun ω => ∑ n ∈ Finset.Icc 1 N, d n ω) ≤
      boundedEnergyConstant a r χ * s := by
  let e : ℕ → Ω → E := fun n ω => s⁻¹ • d n ω
  have hscale (n : ℕ) (ω : Ω) : ‖e n ω‖ ^ a = (s⁻¹) ^ a * ‖d n ω‖ ^ a := by
    dsimp only [e]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hs.le),
      Real.mul_rpow (inv_nonneg.mpr hs.le) (norm_nonneg _)]
  have headapt : ∀ n, 0 < n → n ≤ N → F.AdaptedAt n (e n) := by
    intro n hn hnN ω η hωη
    dsimp only [e]
    rw [hadapt n hn hnN hωη]
  have hezero : ∀ n, 0 < n → n ≤ N →
      HasZeroConditionalSum μ (F.part (n - 1)) (e n) := by
    intro n hn hnN
    exact (hzero n hn hnN).predictable_smul (fun _ => s⁻¹) (fun _ => rfl)
  have hepred : ∀ n, 0 < n → n ≤ N → F.AdaptedAt (n - 1) (fun ω => ‖e n ω‖) := by
    intro n hn hnN ω η hωη
    dsimp only [e]
    have hnorm : ‖d n ω‖ = ‖d n η‖ := hpred n hn hnN hωη
    rw [norm_smul, norm_smul, hnorm]
  have heenergy : ∀ ω, (∑ n ∈ Finset.Icc 1 N, ‖e n ω‖ ^ a) ≤ 1 := by
    intro ω
    simp_rw [hscale]
    rw [← Finset.mul_sum]
    calc
      _ ≤ (s⁻¹) ^ a * s ^ a :=
        mul_le_mul_of_nonneg_left (henergy ω) (Real.rpow_nonneg (inv_nonneg.mpr hs.le) _)
      _ = 1 := by
        rw [← Real.mul_rpow (inv_nonneg.mpr hs.le) hs.le, inv_mul_cancel₀ hs.ne']
        exact Real.one_rpow a
  have h := finiteUpperL2_bounded_energy ha har hχ hUpper μ F e N headapt hezero hepred heenergy
  have hsum : (fun ω => ∑ n ∈ Finset.Icc 1 N, e n ω) =
      fun ω => s⁻¹ • ∑ n ∈ Finset.Icc 1 N, d n ω := by
    funext ω
    simp only [e, Finset.smul_sum]
  rw [hsum, finiteL2Norm_smul, abs_of_pos (inv_pos.mpr hs)] at h
  have hmul := mul_le_mul_of_nonneg_left h hs.le
  rw [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul] at hmul
  simpa only [mul_comm] using hmul

theorem finiteUpperL2_budget_L2 {a r χ s : ℝ}
    (ha : 0 < a) (har : a < r) (hχ : 0 ≤ χ) (hs : 0 < s)
    (hUpper : FiniteUpperL2 E r χ) (μ : FiniteLaw Ω)
    (F : FinitePartitionFiltration Ω) (d : ℕ → Ω → E) (N : ℕ)
    (hadapt : ∀ n, 0 < n → n ≤ N → F.AdaptedAt n (d n))
    (hzero : ∀ n, 0 < n → n ≤ N → HasZeroConditionalSum μ (F.part (n - 1)) (d n))
    (hpred : ∀ n, 0 < n → n ≤ N → F.AdaptedAt (n - 1) (fun ω => ‖d n ω‖)) :
    finiteL2Norm μ
      (partialSumProcess (fun n ω =>
        budgetCoefficient (fun k η => ‖d k η‖ ^ a) (s ^ a) n ω • d n ω) N) ≤
      boundedEnergyConstant a r χ * s := by
  let w : ℕ → Ω → ℝ := fun n ω => ‖d n ω‖ ^ a
  let c : ℕ → Ω → ℝ := budgetCoefficient w (s ^ a)
  let e : ℕ → Ω → E := fun n ω => c n ω • d n ω
  have hw : ∀ n, 0 < n → n ≤ N → F.AdaptedAt (n - 1) (w n) := by
    intro n hn hnN ω η hωη
    dsimp only [w]
    have hnorm : ‖d n ω‖ = ‖d n η‖ := hpred n hn hnN hωη
    rw [hnorm]
  have hc : ∀ n, n ≤ N → F.AdaptedAt (n - 1) (c n) :=
    fun n hnN => budgetCoefficient_predictable F w N (s ^ a) hw hnN
  have headapt : ∀ n, 0 < n → n ≤ N → F.AdaptedAt n (e n) := by
    intro n hn hnN ω η hωη
    dsimp only [e]
    rw [hc n hnN (F.refines (Nat.sub_le n 1) hωη), hadapt n hn hnN hωη]
  have hezero : ∀ n, 0 < n → n ≤ N →
      HasZeroConditionalSum μ (F.part (n - 1)) (e n) := by
    intro n hn hnN
    exact (hzero n hn hnN).predictable_smul (c n) (hc n hnN)
  have hepred : ∀ n, 0 < n → n ≤ N → F.AdaptedAt (n - 1) (fun ω => ‖e n ω‖) := by
    intro n hn hnN ω η hωη
    dsimp only [e]
    have hnorm : ‖d n ω‖ = ‖d n η‖ := hpred n hn hnN hωη
    rw [norm_smul, norm_smul, hc n hnN hωη, hnorm]
  have heenergy : ∀ ω, (∑ n ∈ Finset.Icc 1 N, ‖e n ω‖ ^ a) ≤ s ^ a := by
    intro ω
    rw [sum_Icc_one_eq_sum_range_succ]
    exact budgetTransform_energy_le d ha (Real.rpow_nonneg hs.le _) N ω
  have h := finiteUpperL2_bounded_energy_scale ha har hχ hs hUpper μ F e N
    headapt hezero hepred heenergy
  have hsum : (fun ω => ∑ n ∈ Finset.Icc 1 N, e n ω) = partialSumProcess e N := by
    funext ω
    unfold partialSumProcess
    exact sum_Icc_one_eq_sum_range_succ (fun n => e n ω) N
  rw [hsum] at h
  exact h

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteFirstCrossing
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity
namespace FinitePartitionFiltration

variable {Ω E : Type*} [SeminormedAddCommGroup E]

attribute [local instance] Classical.propDecidable

theorem firstCrossing_le (M : ℕ → Ω → E) (N : ℕ) (t : ℝ) (ω : Ω) :
    firstCrossing M N t ω ≤ N := by
  unfold firstCrossing
  split_ifs with h
  · exact (Nat.find_spec h).1
  · exact le_rfl

theorem firstCrossing_spec (M : ℕ → Ω → E) (N : ℕ) (t : ℝ) (ω : Ω)
    (h : ∃ j : ℕ, j ≤ N ∧ t < ‖M j ω‖) :
    t < ‖M (firstCrossing M N t ω) ω‖ := by
  rw [firstCrossing, dite_eq_left h]
  exact (Nat.find_spec h).2

theorem firstCrossing_eq_terminal_of_no_crossing
    (M : ℕ → Ω → E) (N : ℕ) (t : ℝ) (ω : Ω)
    (h : ¬ ∃ j : ℕ, j ≤ N ∧ t < ‖M j ω‖) :
    firstCrossing M N t ω = N := by
  simp only [firstCrossing, dite_eq_right h]

theorem firstCrossing_le_iff_of_lt (M : ℕ → Ω → E) (t : ℝ)
    {n N : ℕ} (hn : n < N) (ω : Ω) :
    firstCrossing M N t ω ≤ n ↔ ∃ j : ℕ, j ≤ n ∧ t < ‖M j ω‖ := by
  constructor
  · intro hle
    by_cases hex : ∃ j : ℕ, j ≤ N ∧ t < ‖M j ω‖
    · exact ⟨firstCrossing M N t ω, hle, firstCrossing_spec M N t ω hex⟩
    · rw [firstCrossing_eq_terminal_of_no_crossing M N t ω hex] at hle
      exact False.elim ((Nat.not_le_of_gt hn) hle)
  · rintro ⟨j, hj, hc⟩
    have hjN : j ≤ N := hj.trans hn.le
    have hex : ∃ k : ℕ, k ≤ N ∧ t < ‖M k ω‖ := ⟨j, hjN, hc⟩
    rw [firstCrossing, dite_eq_left hex]
    exact (Nat.find_min' hex ⟨hjN, hc⟩).trans hj

theorem isStoppingTime_firstCrossing (F : FinitePartitionFiltration Ω)
    (M : ℕ → Ω → E) (N : ℕ) (t : ℝ)
    (hM : ∀ j : ℕ, j ≤ N → F.AdaptedAt j (M j)) :
    F.IsStoppingTime (firstCrossing M N t) := by
  intro n ω η hωη
  by_cases hN : N ≤ n
  · exact ⟨fun _ => (firstCrossing_le M N t η).trans hN,
      fun _ => (firstCrossing_le M N t ω).trans hN⟩
  · have hn : n < N := Nat.lt_of_not_ge hN
    rw [firstCrossing_le_iff_of_lt M t hn ω,
      firstCrossing_le_iff_of_lt M t hn η]
    have heq (j : ℕ) (hj : j ≤ n) : M j ω = M j η :=
      hM j (hj.trans hn.le) (F.refines hj hωη)
    constructor
    · rintro ⟨j, hj, hc⟩
      exact ⟨j, hj, by simpa only [heq j hj] using hc⟩
    · rintro ⟨j, hj, hc⟩
      exact ⟨j, hj, by simpa only [heq j hj] using hc⟩

end FinitePartitionFiltration
end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteMartingaleMaximal
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

variable {Ω E : Type*} [Fintype Ω]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : FinitePartitionFiltration Ω} {μ : FiniteLaw Ω}
variable {M : ℕ → Ω → E} {N : ℕ} {t : ℝ}

theorem finite_martingale_maximal_sq (hM : F.IsMartingaleUpTo μ M N) (ht : 0 < t) :
    t ^ (2 : ℕ) * μ.prob (fun ω => ∃ j : ℕ, j ≤ N ∧ t < ‖M j ω‖) ≤
      μ.expect (fun ω => ‖M N ω‖ ^ (2 : ℕ)) := by
  classical
  let τ := FinitePartitionFiltration.firstCrossing M N t
  have hτ : F.IsStoppingTime τ := F.isStoppingTime_firstCrossing M N t hM.1
  have hτN : ∀ ω, τ ω ≤ N := FinitePartitionFiltration.firstCrossing_le M N t
  calc
    t ^ (2 : ℕ) * μ.prob (fun ω => ∃ j : ℕ, j ≤ N ∧ t < ‖M j ω‖) =
        μ.expect (fun ω => if ∃ j : ℕ, j ≤ N ∧ t < ‖M j ω‖
          then t ^ (2 : ℕ) else 0) := by
      unfold FiniteLaw.prob FiniteLaw.expect
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _
      by_cases h : ∃ j : ℕ, j ≤ N ∧ t < ‖M j ω‖ <;> simp [h, mul_comm]
    _ ≤ μ.expect (fun ω => ‖M (τ ω) ω‖ ^ (2 : ℕ)) := by
      apply μ.expect_mono
      intro ω
      by_cases h : ∃ j : ℕ, j ≤ N ∧ t < ‖M j ω‖
      · rw [ite_eq_left h]
        have hc : t < ‖M (τ ω) ω‖ :=
          FinitePartitionFiltration.firstCrossing_spec M N t ω h
        nlinarith only [hc, ht, norm_nonneg (M (τ ω) ω)]
      · rw [ite_eq_right h]
        exact sq_nonneg _
    _ ≤ _ := hM.expect_stopped_norm_sq_le hτ hτN

theorem finite_martingale_maximal_sq_le_l2 (hM : F.IsMartingaleUpTo μ M N)
    (ht : 0 < t) :
    t ^ (2 : ℕ) * μ.prob (fun ω => ∃ j : ℕ, j ≤ N ∧ t < ‖M j ω‖) ≤
      finiteL2Norm μ (M N) ^ (2 : ℕ) := by
  rw [finiteL2Norm_sq]
  exact finite_martingale_maximal_sq hM ht

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_TailMoment
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

theorem weighted_tail_power_le {Ω : Type*} [Fintype Ω]
    (w F : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hF : ∀ ω, 0 ≤ F ω)
    {c p : ℝ} (hc : 0 ≤ c) (hp : 0 ≤ p) :
    c ^ p * (∑ ω, if c ≤ F ω then w ω else 0) ≤
      ∑ ω, w ω * (F ω) ^ p := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ω _
  by_cases h : c ≤ F ω
  · simp only [ite_eq_left h]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hc h hp) (hw ω)
  · simp only [ite_eq_right h, mul_zero]
    exact mul_nonneg (hw ω) (Real.rpow_nonneg (hF ω) p)

theorem FiniteLaw.tail_power_mul_prob_le {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (F : Ω → ℝ) (hF : ∀ ω, 0 ≤ F ω)
    {c p : ℝ} (hc : 0 ≤ c) (hp : 0 ≤ p) :
    c ^ p * μ.prob (fun ω => c ≤ F ω) ≤ μ.expect (fun ω => (F ω) ^ p) := by
  classical
  exact weighted_tail_power_le μ.mass F μ.mass_nonneg hF hc hp

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteTruncationTail
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

variable {Ω E : Type*} [Fintype Ω]

namespace FiniteLaw

private theorem prob_le_one_FiniteTruncationTail (μ : FiniteLaw Ω) (A : Ω → Prop) : μ.prob A ≤ 1 := by
  calc
    _ ≤ ∑ ω, μ.mass ω := by
      apply Finset.sum_le_sum
      intro ω _
      by_cases h : A ω
      · simp only [ite_eq_left h, le_refl]
      · simpa only [ite_eq_right h] using μ.mass_nonneg ω
    _ = 1 := μ.sum_mass

theorem prob_le_add_of_imp_or (μ : FiniteLaw Ω) (A C D : Ω → Prop)
    (h : ∀ ω, A ω → C ω ∨ D ω) : μ.prob A ≤ μ.prob C + μ.prob D := by
  unfold prob
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hA : A ω
  · rcases h ω hA with hC | hD
    · by_cases hD : D ω <;> simp only [ite_eq_left hA, ite_eq_left hC, hD, ite_true, ite_false]
      · exact le_add_of_nonneg_right (μ.mass_nonneg ω)
      · simp only [add_zero, le_refl]
    · by_cases hC : C ω <;> simp only [ite_eq_left hA, ite_eq_left hD, hC, ite_true, ite_false]
      · exact le_add_of_nonneg_left (μ.mass_nonneg ω)
      · simp only [zero_add, le_refl]
  · simp only [ite_eq_right hA]
    exact add_nonneg (by split_ifs <;> first | exact μ.mass_nonneg ω | exact le_rfl)
      (by split_ifs <;> first | exact μ.mass_nonneg ω | exact le_rfl)

end FiniteLaw

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finite_budget_maximal_prob_le (μ : FiniteLaw Ω)
    (F : FinitePartitionFiltration Ω) (d : ℕ → Ω → E) (w : ℕ → Ω → ℝ)
    (N : ℕ) {S t : ℝ} (hS : 0 < S) (ht : 0 < t)
    (hadapt : ∀ j, 0 < j → j ≤ N → F.AdaptedAt j (d j))
    (hzero : ∀ j, 0 < j → j ≤ N →
      HasZeroConditionalSum μ (F.part (j - 1)) (d j))
    (hw : ∀ j ω, 0 ≤ w j ω)
    (hwpred : ∀ j, 0 < j → j ≤ N → F.AdaptedAt (j - 1) (w j)) :
    μ.prob (fun ω => ∃ j : ℕ, j ≤ N ∧ t < ‖partialSumProcess d j ω‖) ≤
      μ.expect (cumulativeCost w N) / S +
        finiteL2Norm μ
          (partialSumProcess (fun j ω => budgetCoefficient w S j ω • d j ω) N) ^
            (2 : ℕ) / t ^ (2 : ℕ) := by
  let M := partialSumProcess (fun j ω => budgetCoefficient w S j ω • d j ω)
  have hM : F.IsMartingaleUpTo μ M N :=
    budgetTransform_isMartingale F μ d w N S hadapt hzero hwpred
  have hcost : ∀ ω, 0 ≤ cumulativeCost w N ω := by
    intro ω
    exact Finset.sum_nonneg (fun j _ => hw (j + 1) ω)
  have hmarkov : S * μ.prob (fun ω => S ≤ cumulativeCost w N ω) ≤
      μ.expect (cumulativeCost w N) := by
    simpa only [Real.rpow_one] using
      μ.tail_power_mul_prob_le (cumulativeCost w N) hcost hS.le
        (show (0 : ℝ) ≤ 1 by norm_num)
  have hmax := finite_martingale_maximal_sq_le_l2 hM ht
  calc
    _ ≤ μ.prob (fun ω => S ≤ cumulativeCost w N ω) +
        μ.prob (fun ω => ∃ j : ℕ, j ≤ N ∧ t < ‖M j ω‖) := by
      apply μ.prob_le_add_of_imp_or
      intro ω hω
      by_cases hbad : S ≤ cumulativeCost w N ω
      · exact Or.inl hbad
      · right
        obtain ⟨j, hjN, hj⟩ := hω
        refine ⟨j, hjN, ?_⟩
        have heq : M j ω = partialSumProcess d j ω :=
          budgetTransform_eq_of_cost_le d w hw hjN (le_of_lt (lt_of_not_ge hbad))
        rwa [heq]
    _ ≤ _ := by
      apply add_le_add
      · apply (le_div_iff₀ hS).mpr
        simpa only [mul_comm] using hmarkov
      · apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
        simpa only [mul_comm] using hmax

theorem finite_budget_truncation_tail (μ : FiniteLaw Ω)
    (F : FinitePartitionFiltration Ω) (d : ℕ → Ω → E) (N : ℕ)
    {a B : ℝ} (ha : 1 < a) (ha2 : a ≤ 2) (hB : 0 ≤ B)
    (hadapt : ∀ j, 0 < j → j ≤ N → F.AdaptedAt j (d j))
    (hzero : ∀ j, 0 < j → j ≤ N →
      HasZeroConditionalSum μ (F.part (j - 1)) (d j))
    (hnorm : ∀ j, 0 < j → j ≤ N →
      F.AdaptedAt (j - 1) (fun ω => ‖d j ω‖))
    (henergy : μ.expect (cumulativeCost (fun j ω => ‖d j ω‖ ^ a) N) ≤ 1)
    (hBound : ∀ s : ℝ, 0 < s →
      finiteL2Norm μ (partialSumProcess (fun j ω =>
        budgetCoefficient (fun k η => ‖d k η‖ ^ a) (s ^ a) j ω • d j ω) N) ≤ B * s)
    {t : ℝ} (ht : 0 < t) :
    μ.prob (fun ω => ∃ j : ℕ, j ≤ N ∧ t < ‖partialSumProcess d j ω‖) ≤
      (1 + B ^ (2 : ℕ)) / t ^ (a / 2) := by
  have hw : ∀ j ω, 0 ≤ ‖d j ω‖ ^ a :=
    fun j ω => Real.rpow_nonneg (norm_nonneg _) _
  have hwpred : ∀ j, 0 < j → j ≤ N →
      F.AdaptedAt (j - 1) (fun ω => ‖d j ω‖ ^ a) := by
    intro j hj hjN ω η hωη
    exact congrArg (fun x : ℝ => x ^ a) (hnorm j hj hjN hωη)
  have htPow : 0 < t ^ (a / 2) := Real.rpow_pos_of_pos ht _
  by_cases ht1 : 1 ≤ t
  · have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
    have hsPow : 0 < (Real.sqrt t) ^ a := Real.rpow_pos_of_pos hs _
    have hsq := (sq_le_sq₀
      (finiteL2Norm_nonneg μ (partialSumProcess (fun j ω =>
        budgetCoefficient (fun k η => ‖d k η‖ ^ a) ((Real.sqrt t) ^ a) j ω •
          d j ω) N)) (mul_nonneg hB hs.le)).mpr (hBound (Real.sqrt t) hs)
    have hsplit := finite_budget_maximal_prob_le μ F d (fun j ω => ‖d j ω‖ ^ a)
      N hsPow ht hadapt hzero hw hwpred
    have hroot : (Real.sqrt t) ^ a = t ^ (a / 2) :=
      (Real.rpow_div_two_eq_sqrt a ht.le).symm
    have hquot : (B * Real.sqrt t) ^ (2 : ℕ) / t ^ (2 : ℕ) =
        B ^ (2 : ℕ) / t := by
      rw [mul_pow, Real.sq_sqrt ht.le]
      field_simp [ne_of_gt ht]
    have hden : t ^ (a / 2) ≤ t := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le ht1 (show a / 2 ≤ 1 by linarith)
    calc
      _ ≤ 1 / (Real.sqrt t) ^ a +
          (B * Real.sqrt t) ^ (2 : ℕ) / t ^ (2 : ℕ) :=
        hsplit.trans (add_le_add
          (div_le_div_of_nonneg_right henergy hsPow.le)
          (div_le_div_of_nonneg_right hsq (sq_nonneg t)))
      _ = 1 / t ^ (a / 2) + B ^ (2 : ℕ) / t := by rw [hroot, hquot]
      _ ≤ 1 / t ^ (a / 2) + B ^ (2 : ℕ) / t ^ (a / 2) :=
        add_le_add le_rfl (div_le_div_of_nonneg_left (sq_nonneg B) htPow hden)
      _ = _ := (add_div _ _ _).symm
  · apply (μ.prob_le_one_FiniteTruncationTail _).trans
    apply (le_div_iff₀ htPow).mpr
    simp only [one_mul]
    exact (Real.rpow_le_one ht.le (le_of_lt (lt_of_not_ge ht1))
      (by linarith : 0 ≤ a / 2)).trans (le_add_of_nonneg_right (sq_nonneg B))

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_DyadicWeakMaxFromUpperL2
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem dyadicDifference_norm_predictable {N : ℕ} (φ : DyadicAtom N → E)
    (n : ℕ) (hn : 0 < n) (hnN : n ≤ N) :
    (dyadicFiltration N).AdaptedAt (n - 1)
      (fun ω => ‖finiteDifference (dyadicProcess φ) n ω‖) := by
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ n =>
      have hnN' : n < N := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hnN
      have hd : finiteDifference (dyadicProcess φ) (n + 1) =
          dyadicIncrement φ (⟨n, hnN'⟩ : Fin N) := by
        funext ω
        rw [dyadicProcess_difference_succ, dite_eq_left hnN']
      simp only [Nat.add_sub_cancel, hd]
      intro ω η hωη
      exact dyadicIncrement_norm_predictable φ (⟨n, hnN'⟩ : Fin N) hωη

theorem dyadicDifference_expected_cost {N : ℕ} (φ : DyadicAtom N → E) (a : ℝ) :
    (dyadicLaw N).expect
      (cumulativeCost (fun n ω => ‖finiteDifference (dyadicProcess φ) n ω‖ ^ a) N) =
      ∑ j : Fin N, finiteMoment (dyadicLaw N).mass a (dyadicIncrement φ j) := by
  classical
  unfold FiniteLaw.expect cumulativeCost
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro j _
  unfold finiteMoment
  apply Finset.sum_congr rfl
  intro ω _
  rw [dyadicProcess_difference_succ, dite_eq_left j.is_lt]

theorem dyadicProcess_eq_partialSum_of_root_zero {N : ℕ} (φ : DyadicAtom N → E)
    (hroot : dyadicRoot φ = 0) :
    dyadicProcess φ = partialSumProcess (finiteDifference (dyadicProcess φ)) := by
  funext n ω
  simpa only [dyadicProcess_zero, hroot, zero_add, partialSumProcess] using
    finiteDifference_telescope (dyadicProcess φ) n ω

theorem finiteUpperL2_normalizedWeakMax {a r χ : ℝ}
    (ha : 1 < a) (har : a < r) (hr2 : r ≤ 2) (hχ : 0 ≤ χ)
    (hUpper : FiniteUpperL2 E r χ) :
    DyadicNormalizedWeakMax E a (1 + (boundedEnergyConstant a r χ) ^ (2 : ℕ)) := by
  intro N φ hroot hinput t ht
  let d := finiteDifference (dyadicProcess φ)
  have hM := dyadicProcess_isMartingale φ N
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hadapt : ∀ n, 0 < n → n ≤ N → (dyadicFiltration N).AdaptedAt n (d n) :=
    fun n _ hnN => hM.difference_adapted hnN
  have hzero : ∀ n, 0 < n → n ≤ N →
      HasZeroConditionalSum (dyadicLaw N) ((dyadicFiltration N).part (n - 1)) (d n) :=
    hM.2
  have hnorm : ∀ n, 0 < n → n ≤ N →
      (dyadicFiltration N).AdaptedAt (n - 1) (fun ω => ‖d n ω‖) :=
    dyadicDifference_norm_predictable φ
  have henergy : (dyadicLaw N).expect (cumulativeCost (fun n ω => ‖d n ω‖ ^ a) N) ≤ 1 := by
    change (dyadicLaw N).expect
      (cumulativeCost (fun n ω => ‖finiteDifference (dyadicProcess φ) n ω‖ ^ a) N) ≤ 1
    rw [dyadicDifference_expected_cost]
    have hid := dyadicInputMoment φ a
    have hroot_nonneg : 0 ≤ ‖dyadicRoot φ‖ ^ a := Real.rpow_nonneg (norm_nonneg _) _
    linarith
  have hBound (s : ℝ) (hs : 0 < s) :
      finiteL2Norm (dyadicLaw N) (partialSumProcess (fun n ω =>
        budgetCoefficient (fun k η => ‖d k η‖ ^ a) (s ^ a) n ω • d n ω) N) ≤
          boundedEnergyConstant a r χ * s :=
    finiteUpperL2_budget_L2 ha0 har hχ hs hUpper (dyadicLaw N) (dyadicFiltration N)
      d N hadapt hzero hnorm
  have h := finite_budget_truncation_tail (dyadicLaw N) (dyadicFiltration N) d N
    ha (har.le.trans hr2) (boundedEnergyConstant_nonneg ha0 har hχ)
    hadapt hzero hnorm henergy hBound ht
  simpa only [d, ← dyadicProcess_eq_partialSum_of_root_zero φ hroot] using h

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FinitePowerMeanBound
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

theorem sum_le_of_sum_pow_le {n q : ℕ} (hq : 2 ≤ q)
    {D B : ℝ} (hD : 0 < D) (hB : 0 ≤ B)
    (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hpow : ∑ i, r i ^ q ≤ D * B ^ q) :
    ∑ i, r i ≤ D ^ (1 / (q : ℝ)) *
      (n : ℝ) ^ (1 - 1 / (q : ℝ)) * B := by
  have hqR : (1 : ℝ) < (q : ℝ) :=
    Nat.one_lt_cast.mpr (lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hq)
  have hqNat : q ≠ 0 :=
    Nat.ne_of_gt (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hq)
  have hroot_nonneg : (0 : ℝ) ≤ 1 / (q : ℝ) :=
    (one_div_pos.mpr (zero_lt_one.trans hqR)).le
  have hpq := Real.HolderConjugate.conjExponent hqR
  have hexponent : 1 / Real.conjExponent (q : ℝ) = 1 - 1 / (q : ℝ) := by
    simpa only [one_div] using hpq.one_sub_inv.symm
  have hholder :
      (∑ i, r i) ≤ (∑ i, r i ^ q) ^ (1 / (q : ℝ)) *
        (n : ℝ) ^ (1 - 1 / (q : ℝ)) := by
    have hh := finite_weighted_holder_univ
      (w := fun _ : Fin n => (1 : ℝ)) (a := r) (b := fun _ => (1 : ℝ))
      hpq (fun _ => zero_le_one) hr (fun _ => zero_le_one)
    simpa only [one_mul, mul_one, Real.one_rpow, Real.rpow_natCast,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      hexponent] using hh
  have hsum_nonneg : 0 ≤ ∑ i, r i ^ q :=
    Finset.sum_nonneg (fun i _ => pow_nonneg (hr i) q)
  have hroot : (∑ i, r i ^ q) ^ (1 / (q : ℝ)) ≤ D ^ (1 / (q : ℝ)) * B := by
    calc
      (∑ i, r i ^ q) ^ (1 / (q : ℝ)) ≤ (D * B ^ q) ^ (1 / (q : ℝ)) :=
        Real.rpow_le_rpow hsum_nonneg hpow hroot_nonneg
      _ = D ^ (1 / (q : ℝ)) * (B ^ q) ^ (1 / (q : ℝ)) :=
        Real.mul_rpow hD.le (pow_nonneg hB q)
      _ = D ^ (1 / (q : ℝ)) * B := by
        simp only [one_div, Real.pow_rpow_inv_natCast hB hqNat]
  calc
    (∑ i, r i) ≤ (∑ i, r i ^ q) ^ (1 / (q : ℝ)) *
        (n : ℝ) ^ (1 - 1 / (q : ℝ)) := hholder
    _ ≤ (D ^ (1 / (q : ℝ)) * B) * (n : ℝ) ^ (1 - 1 / (q : ℝ)) :=
      mul_le_mul_of_nonneg_right hroot (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    _ = D ^ (1 / (q : ℝ)) * (n : ℝ) ^ (1 - 1 / (q : ℝ)) * B := by ring

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteL2CoefficientAdapter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

open scoped BigOperators ENNReal

variable {E : Type*} [NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]

theorem finiteL2ToSequence_norm_sq {m : ℕ} (μ : FiniteLaw (Fin m)) (f : Fin m → E) :
    ‖finiteL2ToSequence μ f‖ ^ 2 = μ.expect (fun i => ‖f i‖ ^ (2 : ℕ)) := by
  classical
  let e : Fin m ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  let g : ℕ → E := fun k => if hk : k < m then
    Real.sqrt (μ.mass ⟨k, hk⟩) • f ⟨k, hk⟩ else 0
  let s : Finset ℕ := Finset.univ.map e
  have hg (i : Fin m) : g (e i) = Real.sqrt (μ.mass i) • f i := by
    simp [g, e, i.is_lt]
  have hleft : (∑ k ∈ s, lp.single (2 : ℝ≥0∞) k (g k)) =
      finiteL2ToSequence μ f := by
    rw [Finset.sum_map]
    simp only [hg]
    rfl
  have hright : (∑ k ∈ s, ‖g k‖ ^ (2 : ℕ)) =
      μ.expect (fun i => ‖f i‖ ^ (2 : ℕ)) := by
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro i _
    rw [hg, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      mul_pow, Real.sq_sqrt (μ.mass_nonneg i)]
  have h := lp.norm_sum_single (p := (2 : ℝ≥0∞))
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal) g s
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  rw [hleft, hright] at h
  exact h

@[simp] theorem finiteL2ToSequence_norm {m : ℕ} (μ : FiniteLaw (Fin m))
    (f : Fin m → E) : ‖finiteL2ToSequence μ f‖ = finiteL2Norm μ f := by
  apply (sq_eq_sq₀ (norm_nonneg _) (finiteL2Norm_nonneg μ f)).mp
  rw [finiteL2ToSequence_norm_sq, finiteL2Norm_sq]

section FiniteProcess

variable {Ω : Type*} [sectionFintypeΩ : Fintype Ω]

omit sectionNormedSpaceℝE in
private theorem finiteL2Norm_eq_of_positive_mass [NormedSpace ℝ E] (μ : FiniteLaw Ω)
    (f g : Ω → E) (h : ∀ ω, 0 < μ.mass ω → f ω = g ω) :
    finiteL2Norm μ f = finiteL2Norm μ g := by
  apply congrArg Real.sqrt
  apply Finset.sum_congr rfl
  intro ω _
  change μ.mass ω * ‖f ω‖ ^ (2 : ℕ) = μ.mass ω * ‖g ω‖ ^ (2 : ℕ)
  by_cases hz : μ.mass ω = 0
  · simp only [hz, zero_mul]
  · rw [h ω (lt_of_le_of_ne (μ.mass_nonneg ω) (Ne.symm hz))]

theorem FinitePartitionFiltration.IsMartingaleUpTo.finiteL2Norm_le_terminal
    {F : FinitePartitionFiltration Ω} {μ : FiniteLaw Ω}
    {M : ℕ → Ω → E} {N j : ℕ} (hM : F.IsMartingaleUpTo μ M N) (hj : j ≤ N) :
    finiteL2Norm μ (M j) ≤ finiteL2Norm μ (M N) := by
  have heq : finiteL2Norm μ (M j) =
      finiteL2Norm μ (F.conditionalProcess μ (M N) j) := by
    apply finiteL2Norm_eq_of_positive_mass
    intro ω hω
    exact (hM.conditional_terminal_of_mass_pos hj ω hω).symm
  rw [heq]
  exact F.finiteL2Norm_conditionalProcess_le μ (M N) j

omit sectionFintypeΩ in
theorem finiteCoefficientProcess_terminal [Fintype Ω] {N : ℕ} (M : ℕ → Ω → E)
    (a : Fin (N + 1) → ℝ) (ω : Ω) :
    finiteCoefficientProcess M a N ω = ∑ i, a i • finiteDifference M i.val ω := by
  apply Finset.sum_congr rfl
  intro i _
  exact ite_eq_left (Nat.le_of_lt_succ i.is_lt)

omit sectionFintypeΩ in
theorem finiteCoefficientProcess_difference [Fintype Ω] {N j : ℕ} (M : ℕ → Ω → E)
    (a : Fin (N + 1) → ℝ) (hj : 0 < j) (hjN : j ≤ N) (ω : Ω) :
    finiteDifference (finiteCoefficientProcess M a) j ω =
      a ⟨j, Nat.lt_succ_of_le hjN⟩ • finiteDifference M j ω := by
  let l : Fin (N + 1) := ⟨j, Nat.lt_succ_of_le hjN⟩
  rw [finiteDifference, ite_eq_right (Nat.ne_of_gt hj)]
  change (∑ i : Fin (N + 1), if i.val ≤ j then a i • finiteDifference M i.val ω else 0) -
    (∑ i : Fin (N + 1), if i.val ≤ j - 1 then a i • finiteDifference M i.val ω else 0) = _
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ i : Fin (N + 1), if i = l then a l • finiteDifference M j ω else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i = l
      · subst i
        have hjprev : ¬ j ≤ j - 1 := by omega
        simp [l, hjprev]
      · have hiv : i.val ≠ j := fun h => hi (Fin.ext h)
        have hiff : i.val ≤ j ↔ i.val ≤ j - 1 := by omega
        simp only [hiff, sub_self, ite_eq_right hi]
    _ = _ := by simp [l]

theorem finiteCoefficientProcess_isMartingale {N : ℕ}
    {F : FinitePartitionFiltration Ω} {μ : FiniteLaw Ω} {M : ℕ → Ω → E}
    (hM : F.IsMartingaleUpTo μ M N) (a : Fin (N + 1) → ℝ) :
    F.IsMartingaleUpTo μ (finiteCoefficientProcess M a) N := by
  constructor
  · intro j hj ω η hωη
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.val ≤ j
    · simp only [ite_eq_left hi]
      rw [hM.difference_adapted (Nat.le_of_lt_succ i.is_lt) (F.refines hi hωη)]
    · simp only [ite_eq_right hi]
  · intro j hj hjN
    have hdiff : finiteDifference (finiteCoefficientProcess M a) j =
        fun ω => a ⟨j, Nat.lt_succ_of_le hjN⟩ • finiteDifference M j ω :=
      funext (finiteCoefficientProcess_difference M a hj hjN)
    rw [hdiff]
    exact (hM.2 j hj hjN).predictable_smul (fun _ => a ⟨j, Nat.lt_succ_of_le hjN⟩)
      (fun {_ _} _ => rfl)

end FiniteProcess

theorem finiteDifference_coefficientMonotone {m N : ℕ}
    {μ : FiniteLaw (Fin m)} {F : FinitePartitionFiltration (Fin m)}
    {M : ℕ → Fin m → E} (hM : F.IsMartingaleUpTo μ M N) :
    CoefficientMonotone (fun i : Fin (N + 1) =>
      finiteL2ToSequence μ (finiteDifference M i.val)) := by
  intro a k hk
  rw [one_mul]
  have hsum (c : Fin (N + 1) → ℝ) :
      finiteL2ToSequence μ (fun ω => ∑ i, c i • finiteDifference M i.val ω) =
        ∑ i, c i • finiteL2ToSequence μ (finiteDifference M i.val) := by
    have heq : (fun ω => ∑ i : Fin (N + 1), c i • finiteDifference M i.val ω) =
        ∑ i : Fin (N + 1), c i • finiteDifference M i.val := by
      funext ω
      simp only [Finset.sum_apply, Pi.smul_apply]
    rw [heq, map_sum]
    simp only [map_smul]
  have hpref := hsum (fun i => if i.val < k then a i else 0)
  simp only [ite_smul, zero_smul] at hpref
  rw [← hpref, ← hsum a, finiteL2ToSequence_norm, finiteL2ToSequence_norm]
  by_cases hk0 : k = 0
  · subst k
    simpa only [Nat.not_lt_zero, ite_false, Finset.sum_const_zero, finiteL2Norm_zero] using
      finiteL2Norm_nonneg μ (fun ω => ∑ i, a i • finiteDifference M i.val ω)
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  have hprefProcess :
      (fun ω => ∑ i : Fin (N + 1), if i.val < k then
        a i • finiteDifference M i.val ω else 0) =
        finiteCoefficientProcess M a (k - 1) := by
    funext ω
    apply Finset.sum_congr rfl
    intro i _
    have hi : i.val < k ↔ i.val ≤ k - 1 := by omega
    simp only [hi]
  have hfullProcess : (fun ω => ∑ i, a i • finiteDifference M i.val ω) =
      finiteCoefficientProcess M a N :=
    (funext (finiteCoefficientProcess_terminal M a)).symm
  rw [hprefProcess, hfullProcess]
  exact (finiteCoefficientProcess_isMartingale hM a).finiteL2Norm_le_terminal (by omega)

theorem sum_finiteL2ToSequence_differences {m : ℕ} (μ : FiniteLaw (Fin m))
    (M : ℕ → Fin m → E) (N : ℕ) :
    (∑ i : Fin (N + 1), finiteL2ToSequence μ (finiteDifference M i.val)) =
      finiteL2ToSequence μ (M N) := by
  rw [← map_sum]
  apply congrArg (finiteL2ToSequence μ)
  funext ω
  rw [Finset.sum_apply]
  exact (Finset.sum_range (n := N + 1)
    (fun k : ℕ => finiteDifference M k ω)).symm.trans
      (sum_finiteDifference_eq M N ω)

theorem finiteLowerL2_of_sequence_obstruction
    (h : FiniteTriangularObstruction (SequenceL2 E)) :
    ∃ s : ℝ, 2 ≤ s ∧ ∃ χ : ℝ, 1 ≤ χ ∧ FiniteLowerL2 E s χ := by
  obtain ⟨q, hq, D, hD, hpower⟩ :=
    h.coefficient_lower_power (K := 2) (by norm_num)
  have hqreal : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  let χ : ℝ := max 1 (D ^ (1 / (q : ℝ)))
  have hχ : D ^ (1 / (q : ℝ)) ≤ χ := le_max_right _ _
  refine ⟨(q : ℝ), hqreal, χ, le_max_left _ _, ?_⟩
  intro m μ F M N hM
  let x : Fin (N + 1) → SequenceL2 E := fun i =>
    finiteL2ToSequence μ (finiteDifference M i.val)
  have hx : CoefficientBasic 2 x :=
    (finiteDifference_coefficientMonotone hM).mono (by norm_num)
  have hpow := hpower (N + 1) x hx
  have htotal : (∑ i, x i) = finiteL2ToSequence μ (M N) :=
    sum_finiteL2ToSequence_differences μ M N
  rw [htotal, finiteL2ToSequence_norm] at hpow
  simp only [x, finiteL2ToSequence_norm] at hpow
  have hsum := sum_le_of_sum_pow_le hq hD (finiteL2Norm_nonneg μ (M N))
    (fun i : Fin (N + 1) => finiteL2Norm μ (finiteDifference M i.val))
    (fun i => finiteL2Norm_nonneg μ _) hpow
  have hfinal : (∑ i : Fin (N + 1), finiteL2Norm μ (finiteDifference M i.val)) ≤
      χ * ((N + 1 : ℕ) : ℝ) ^ (1 - 1 / (q : ℝ)) * finiteL2Norm μ (M N) :=
    hsum.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hχ (Real.rpow_nonneg (Nat.cast_nonneg (N + 1)) _))
      (finiteL2Norm_nonneg μ (M N)))
  rw [Finset.sum_range]
  simpa only [Nat.cast_add, Nat.cast_one] using hfinal

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteL2IsometryTransport
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

universe u v w
variable {E : Type u} {G : Type v} {Ω : Type w}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup G] [NormedSpace ℝ G] [sectionFintypeΩ : Fintype Ω]

omit sectionFintypeΩ in
@[simp] theorem finiteDifference_map [Fintype Ω] (T : E →ₗ[ℝ] G) (M : ℕ → Ω → E)
    (j : ℕ) (ω : Ω) :
    finiteDifference (fun n ω => T (M n ω)) j ω = T (finiteDifference M j ω) := by
  by_cases hj : j = 0
  · subst j
    rfl
  · simp only [finiteDifference, ite_eq_right hj, map_sub]

@[simp] theorem finiteL2Norm_linearIsometry (T : E →ₗᵢ[ℝ] G)
    (μ : FiniteLaw Ω) (f : Ω → E) :
    finiteL2Norm μ (fun ω => T (f ω)) = finiteL2Norm μ f := by
  simp only [finiteL2Norm, T.norm_map]

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteMartingaleDuality
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finite_l2_dual_pairing_bound {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (g : Ω → E →L[ℝ] ℝ) (f : Ω → E) :
    |μ.expect (fun ω => g ω (f ω))| ≤ finiteL2Norm μ g * finiteL2Norm μ f := by
  have h := abs_sum_weighted_le_holder Finset.univ
    (w := μ.mass) (a := fun ω => ‖g ω‖) (b := fun ω => ‖f ω‖)
    (c := fun ω => g ω (f ω)) Real.HolderConjugate.two_two
    (fun ω _ => μ.mass_nonneg ω) (fun ω _ => norm_nonneg _)
    (fun ω _ => norm_nonneg _) (by
      intro ω _
      simpa only [Real.norm_eq_abs] using (g ω).le_opNorm (f ω))
  simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow, finiteL2Norm, FiniteLaw.expect] using h

theorem lowerL2_dual_exponent_range {s : ℝ} (hs : 2 ≤ s) :
    1 < s / (s - 1) ∧ s / (s - 1) ≤ 2 := by
  have hd : 0 < s - 1 := by linarith only [hs]
  constructor
  · apply (lt_div_iff₀ hd).mpr
    linarith only [hs]
  · apply (div_le_iff₀ hd).mpr
    linarith only [hs]

theorem finiteLowerL2_dual_upper {s χ : ℝ} (hs : 2 ≤ s) (hχ : 1 ≤ χ)
    (h : FiniteLowerL2 E s χ) :
    FiniteUpperL2 (E →L[ℝ] ℝ) (s / (s - 1)) χ := by
  intro m μ F G N B hB hG hdiff
  have hspos : 0 < s := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hs
  have hsm1 : 0 < s - 1 := by linarith only [hs]
  have hexp : 1 / (s / (s - 1)) = 1 - 1 / s := by
    field_simp [hspos.ne', hsm1.ne']
  let C : ℝ := χ * (N + 1 : ℝ) ^ (1 - 1 / s)
  have hC : 0 ≤ C := mul_nonneg (zero_le_one.trans hχ) (Real.rpow_nonneg (by positivity) _)
  let D : ℝ := finiteL2Norm μ (G N)
  let R : ℝ := χ * (N + 1 : ℝ) ^ (1 / (s / (s - 1))) * B
  change D ≤ R
  by_contra hbound
  let ε : ℝ := (D - R) / 2
  have hε : 0 < ε := half_pos (sub_pos.mpr (lt_of_not_ge hbound))
  obtain ⟨f, hfunit, htest⟩ := exists_weighted_dual_l2_test μ.mass μ.mass_nonneg
    (G N) D (finiteL2Norm_nonneg μ (G N))
    (by simpa only [D, FiniteLaw.expect] using finiteL2Norm_sq μ (G N)) hε
  have hfL2 : finiteL2Norm μ f ≤ 1 := by
    have hsq : finiteL2Norm μ f ^ (2 : ℕ) ≤ 1 := by
      rw [finiteL2Norm_sq]
      exact hfunit
    exact (sq_le_sq₀ (finiteL2Norm_nonneg μ f) zero_le_one).1
      (by simpa only [one_pow] using hsq)
  let V := F.conditionalProcess μ f
  have hV : F.IsMartingaleUpTo μ V N := F.isMartingaleUpTo_conditionalProcess μ f N
  have hVN : finiteL2Norm μ (V N) ≤ 1 :=
    (F.finiteL2Norm_conditionalProcess_le μ f N).trans hfL2
  have hsum : (∑ j ∈ Finset.range (N + 1), finiteL2Norm μ (finiteDifference V j)) ≤ C := by
    calc
      _ ≤ C * finiteL2Norm μ (V N) := h m μ F V N hV
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left hVN hC
      _ = C := mul_one _
  have hpair : μ.expect (fun ω => G N ω (f ω)) ≤ R := by
    calc
      _ = ∑ j ∈ Finset.range (N + 1),
          μ.expect (fun ω => finiteDifference G j ω (finiteDifference V j ω)) :=
        finite_martingale_terminal_pairing hG f
      _ ≤ ∑ j ∈ Finset.range (N + 1), B * finiteL2Norm μ (finiteDifference V j) := by
        apply Finset.sum_le_sum
        intro j hj
        have hGj := hdiff j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
        calc
          _ ≤ |μ.expect (fun ω => finiteDifference G j ω (finiteDifference V j ω))| :=
            le_abs_self _
          _ ≤ finiteL2Norm μ (finiteDifference G j) *
              finiteL2Norm μ (finiteDifference V j) :=
            finite_l2_dual_pairing_bound μ (finiteDifference G j) (finiteDifference V j)
          _ ≤ B * finiteL2Norm μ (finiteDifference V j) :=
            mul_le_mul_of_nonneg_right hGj (finiteL2Norm_nonneg μ _)
      _ = B * ∑ j ∈ Finset.range (N + 1), finiteL2Norm μ (finiteDifference V j) :=
        by rw [Finset.mul_sum]
      _ ≤ B * C := mul_le_mul_of_nonneg_left hsum hB
      _ = R := by dsimp [C, R]; rw [hexp]; ring
  change D - ε ≤ μ.expect (fun ω => G N ω (f ω)) at htest
  dsimp [ε] at htest
  linarith only [htest, hpair, lt_of_not_ge hbound]

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteMartingaleExtrapolation
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finiteUpperL2_extrapolate_synthesis {r χ p : ℝ}
    (_hr : 1 < r) (hr2 : r ≤ 2) (hχ : 1 ≤ χ)
    (hUpper : FiniteUpperL2 E r χ) (hp : 1 < p) (hpr : p < r) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ (N : ℕ) (φ : DyadicAtom N → E),
      finiteMoment (dyadicLaw N).mass p (dyadicSynthesis N φ) ≤
        T ^ p * finiteMoment dyadicInputWeight p φ := by
  have hmax : ∀ a : ℝ, 1 < a → a < r →
      ∃ A : ℝ, 1 ≤ A ∧ DyadicNormalizedWeakMax E a A := by
    intro a ha har
    refine ⟨1 + (boundedEnergyConstant a r χ) ^ (2 : ℕ), ?_, ?_⟩
    · exact le_add_of_nonneg_right (sq_nonneg _)
    · exact finiteUpperL2_normalizedWeakMax ha har hr2 (zero_le_one.trans hχ) hUpper
  obtain ⟨K, hK, hstrong⟩ := dyadic_strong_of_normalizedWeakMax hp hpr hmax
  let T : ℝ := max 1 K
  have hT : 1 ≤ T := le_max_left _ _
  have hKT : K ≤ T ^ p :=
    (le_max_right 1 K).trans (Real.self_le_rpow_of_one_le hT hp.le)
  refine ⟨T, hT, ?_⟩
  intro N φ
  have hinput : 0 ≤ finiteMoment dyadicInputWeight p φ := by
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (dyadicInputWeight_nonneg i)
      (Real.rpow_nonneg (norm_nonneg (φ i)) p))
  exact (hstrong N φ).trans (mul_le_mul_of_nonneg_right hKT hinput)

end MarkovSuperreflexivity

end

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_FiniteLowerL2Cotype
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finiteLowerL2_extrapolate_dyadic {s χ : ℝ}
    (hs : 2 ≤ s) (hχ : 1 ≤ χ) (hLower : FiniteLowerL2 E s χ) :
    ∃ q : ℝ, 2 ≤ q ∧ ∃ A : ℝ, 1 ≤ A ∧ FiniteDyadicCotype E q A := by
  let r : ℝ := s / (s - 1)
  have hrange : 1 < r ∧ r ≤ 2 := lowerL2_dual_exponent_range hs
  have hDual : FiniteUpperL2 (E →L[ℝ] ℝ) r χ := finiteLowerL2_dual_upper hs hχ hLower
  let p : ℝ := (1 + r) / 2
  have hp : 1 < p := by dsimp [p]; linarith only [hrange.1]
  have hpr : p < r := by dsimp [p]; linarith only [hrange.1]
  have hp2 : p ≤ 2 := by dsimp [p]; linarith only [hrange.2]
  obtain ⟨T, hT, hStrong⟩ := finiteUpperL2_extrapolate_synthesis
    hrange.1 hrange.2 hχ hDual hp hpr
  let q : ℝ := p / (p - 1)
  have hpq : p.HolderConjugate q := (Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl
  have hq : 2 ≤ q := by
    apply (le_div_iff₀ (sub_pos.mpr hp)).mpr
    linarith only [hp2]
  exact ⟨q, hq, T ^ q, Real.one_le_rpow hT hpq.symm.pos.le,
    finiteDyadicCotype_of_dual_synthesis hpq hT hStrong⟩

theorem hasEquivalentUCNorm_of_finiteLowerL2 {s χ : ℝ}
    (hs : 2 ≤ s) (hχ : 1 ≤ χ) (hLower : FiniteLowerL2 E s χ) :
    HasEquivalentUCNorm E := by
  obtain ⟨q, hq, A, hA, hCotype⟩ := finiteLowerL2_extrapolate_dyadic hs hχ hLower
  exact hasEquivalentUCNorm_of_finiteDyadicCotype hq hA hCotype

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_RenormedGeometry
attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace Renormed

@[simp] theorem normSeminorm_comp_original (N : EquivalentNorm X) :
    (normSeminorm ℝ (Renormed N)).comp (linearEquiv N).toLinearMap = N.p := by
  ext x
  rfl

@[simp] theorem originalSeminorm_comp_inverse (N : EquivalentNorm X) :
    N.p.comp (linearEquiv N).symm.toLinearMap = normSeminorm ℝ (Renormed N) := by
  ext x
  rfl

end Renormed
end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_StructuralL2Estimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem finiteLowerL2_of_obstruction (h : FiniteTriangularObstruction X) :
    ∃ s : ℝ, 2 ≤ s ∧ ∃ χ : ℝ, 1 ≤ χ ∧ FiniteLowerL2 X s χ :=
  finiteLowerL2_of_sequence_obstruction h.sequenceL2

end MarkovSuperreflexivity

end OAI
end

section
-- module Solutions.OAIS_Markov.MarkovType_JamesEnflo
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

universe u v
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Y : Type v} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem hasEquivalentUCNorm_of_finiteTriangularObstruction_oai
    (h : FiniteTriangularObstruction X) : HasEquivalentUCNorm X := by
  obtain ⟨s, hs, χ, hχ, hLower⟩ := finiteLowerL2_of_obstruction h
  exact hasEquivalentUCNorm_of_finiteLowerL2 hs hχ hLower

end MarkovSuperreflexivity

end OAI
end

theorem solution.{u} : type_of% @OAI.MarkovSuperreflexivity.hasEquivalentUCNorm_of_finiteTriangularObstruction_oai.{u} := @OAI.MarkovSuperreflexivity.hasEquivalentUCNorm_of_finiteTriangularObstruction_oai.{u}
