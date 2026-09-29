-- Prove2me | solution 1 for MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/452305f1-f66d-58aa-9acc-7f9b1115baa1

import Mathlib
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_nilEval_eq_adicEval_of_pow_succ_eq_bot

set_option autoImplicit false

open MvPowerSeries

namespace MvFormalGroup
p2m_export "MvFormalGroup" "adicEval nilEval"
namespace NilEvalBridge
p2m_open "MvFormalGroup"

theorem isAdicComplete_of_pow_eq_bot {C : Type*} [CommRing C] (J : Ideal C) {N : ℕ} (hN : J ^ N = ⊥) :
    IsAdicComplete J C := by
  haveI : IsHausdorff J C := ⟨fun x hx => by
    have := hx N
    rw [hN] at this
    simpa [SModEq.zero] using this⟩
  haveI : IsPrecomplete J C := ⟨fun {f} hf => ⟨f N, fun m => by
    by_cases hm : m ≤ N
    · exact hf hm
    · push Not at hm
      have h1 : f N ≡ f m [SMOD (J ^ N • ⊤ : Submodule C C)] := hf hm.le
      have h2 : (J ^ m • ⊤ : Submodule C C) = ⊥ := by
        rw [show m = N + (m - N) by omega, pow_add, hN, Ideal.bot_mul]; simp
      have h3 : (J ^ N • ⊤ : Submodule C C) = ⊥ := by rw [hN]; simp
      rw [h2]; rw [h3] at h1
      exact h1.symm⟩⟩
  exact ⟨⟩

theorem pow_eq_zero_of_mem {C : Type*} [CommRing C] {J : Ideal C} {n : ℕ} (hJ : J ^ (n + 1) = ⊥) {x : C}
    (hx : x ∈ J) {e : ℕ} (he : n < e) : x ^ e = 0 := by
  have h1 : x ^ (n + 1) ∈ J ^ (n + 1) := Ideal.pow_mem_pow hx _
  rw [hJ, Ideal.mem_bot] at h1
  obtain ⟨k, rfl⟩ : ∃ k, e = n + 1 + k := ⟨e - (n + 1), by omega⟩
  rw [pow_add, h1, zero_mul]

theorem prod_pow_eq_zero_of_not_le {C : Type*} [CommRing C] {σ : Type*} [Finite σ] {J : Ideal C} {n : ℕ}
    (hJ : J ^ (n + 1) = ⊥) {s : σ → C} (hs : ∀ i, s i ∈ J) {d : σ →₀ ℕ}
    (hd : ¬ d ≤ Finsupp.equivFunOnFinite.symm (fun _ => n)) :
    (d.prod fun i e => s i ^ e) = 0 := by
  classical
  simp only [Finsupp.le_def, not_forall, not_le] at hd
  obtain ⟨i, hi⟩ := hd
  have hi' : n < d i := by simpa using hi
  have hmem : i ∈ d.support := by
    rw [Finsupp.mem_support_iff]; omega
  rw [Finsupp.prod, ← Finset.mul_prod_erase _ _ hmem, pow_eq_zero_of_mem hJ (hs i) hi', zero_mul]

end MvFormalGroup.NilEvalBridge

open MvFormalGroup.NilEvalBridge in
theorem solution
    {B : Type} [CommRing B] {σ : Type} [Fintype σ] [DecidableEq σ]
    {B' : Type} [CommRing B'] [Algebra B B'] (J : Ideal B') (n : ℕ) (hJ : J ^ (n + 1) = ⊥)
    (φ : MvPowerSeries σ B) (s : σ → B') (hs : ∀ i, s i ∈ J) :
    MvFormalGroup.nilEval n φ s = MvFormalGroup.adicEval J s φ := by
  classical
  letI : UniformSpace B := ⊥
  letI : WithIdeal B' := ⟨J⟩
  have hIsAdic : IsAdic J := rfl
  haveI : IsAdicComplete J B' := isAdicComplete_of_pow_eq_bot J hJ
  haveI : CompleteSpace B' := ((IsAdic.isAdicComplete_iff hIsAdic).mp ‹IsAdicComplete J B'›).1
  haveI : T2Space B' := ((IsAdic.isAdicComplete_iff hIsAdic).mp ‹IsAdicComplete J B'›).2
  have hcont : Continuous (algebraMap B B') := continuous_of_discreteTopology

  have hev : MvPowerSeries.HasEval s := by
    refine ⟨fun i => ?_, ?_⟩
    · show Filter.Tendsto (fun k => s i ^ k) Filter.atTop (nhds 0)
      rw [(J.hasBasis_nhds_zero_adic).tendsto_right_iff]
      intro m _
      filter_upwards [Filter.eventually_ge_atTop m] with k hk
      exact SetLike.mem_coe.mpr (Ideal.pow_le_pow_right hk (Ideal.pow_mem_pow (hs i) k))
    · rw [Filter.cofinite_eq_bot]
      exact Filter.tendsto_bot

  set box : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => n) with hbox
  have hsum := MvPowerSeries.hasSum_eval₂ hcont hev φ
  have hzero : ∀ d ∉ Finset.Iic box,
      algebraMap B B' (MvPowerSeries.coeff d φ) * (d.prod fun i e => s i ^ e) = 0 := by
    intro d hd
    rw [Finset.mem_Iic] at hd
    rw [prod_pow_eq_zero_of_not_le hJ hs hd, mul_zero]
  have hsum2 : HasSum (fun d : σ →₀ ℕ => algebraMap B B' (MvPowerSeries.coeff d φ) * (d.prod fun i e => s i ^ e))
      (∑ d ∈ Finset.Iic box, algebraMap B B' (MvPowerSeries.coeff d φ) * (d.prod fun i e => s i ^ e)) :=
    hasSum_sum_of_ne_finset_zero hzero
  have heval : MvFormalGroup.adicEval J s φ =
      ∑ d ∈ Finset.Iic box, algebraMap B B' (MvPowerSeries.coeff d φ) * (d.prod fun i e => s i ^ e) := by
    show MvPowerSeries.eval₂ (algebraMap B B') s φ = _
    exact hsum.unique hsum2
  rw [heval]

  show MvPolynomial.aeval s (MvPowerSeries.trunc' B box φ) = _
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  have hsupp : (MvPowerSeries.trunc' B box φ).support ⊆ Finset.Iic box :=
    MvPowerSeries.support_truncFinset_subset φ
  rw [Finset.sum_subset hsupp]
  · refine Finset.sum_congr rfl fun d hd => ?_
    rw [Finset.mem_Iic] at hd
    rw [MvPowerSeries.coeff_trunc', if_pos hd]
    rfl
  · intro d _ hd
    rw [MvPolynomial.notMem_support_iff] at hd
    rw [hd, map_zero, zero_mul]

end S_MvFormalGroup_nilEval_eq_adicEval_of_pow_succ_eq_bot
end P2MW
export P2MW.S_MvFormalGroup_nilEval_eq_adicEval_of_pow_succ_eq_bot (solution)
