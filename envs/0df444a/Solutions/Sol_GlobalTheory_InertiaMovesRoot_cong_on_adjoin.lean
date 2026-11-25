-- Prove2me | solution 1 for GlobalTheory.InertiaMovesRoot.cong_on_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:00:52.588957+00:00
-- url     : https://prove2.me/submissions/1323abd4-6900-46d1-9f64-e618bd3db856

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsCongOfCongOnFixed
import Theorems.Thm_GlobalTheory_InertiaMovesRoot_exists_val_eq_zpow
import Theorems.Thm_GlobalTheory_InertiaMovesRoot_val_term_le_one
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpChar_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDim_lpSp
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDim_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDual_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpSum_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_unr_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_coe_qPow
import Theorems.Thm_GlobalTheory_WeilDeligne_deg_ineIncl
import Theorems.Thm_GlobalTheory_WeilDeligne_qPow_zero
import Theorems.Thm_GlobalTheory_WeilDeligne_unrChar_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpChar_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDim_lpSp
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDim_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDual_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpSum_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.unr_mk
attribute [local simp] GlobalTheory.WeilDeligne.coe_qPow
attribute [local simp] GlobalTheory.WeilDeligne.deg_ineIncl
attribute [local simp] GlobalTheory.WeilDeligne.qPow_zero
attribute [local simp] GlobalTheory.WeilDeligne.unrChar_apply



set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne Pointwise
open GlobalTheory GlobalTheory.InertiaMovesRoot
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
namespace GlobalTheory.InertiaMovesRoot
theorem _root_.solution (h : IsPlaceOver A w) {l : ℕ} (hl : 2 ≤ l) {ϖ : 𝓞 E} (h1 : ϖ ∈ w.asIdeal)
    (h2 : ϖ ∉ w.asIdeal ^ 2) {x : Ω} (hx : x ^ l = algebraMap E Ω (ϖ : E)) :
    x ∉ (⊥ : IntermediateField E Ω) ∧ ∀ (g : Ω ≃ₐ[E] Ω) (b : Ω),
      b ∈ IntermediateField.adjoin E {x} → A.valuation b ≤ 1 → A.valuation (g b - b) < 1 := by
  have hϖ0 : ϖ ≠ 0 := by rintro rfl; exact h2 (zero_mem _)
  have hl0 : l ≠ 0 := by omega
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow hl0, eq_comm, map_eq_zero] at hx
    exact hϖ0 (by simpa using hx)
  set t := A.valuation x with ht
  have htl : A.valuation (algebraMap E Ω (ϖ : E)) = t ^ l := by rw [← hx, map_pow]
  have ht0 : 0 < t := zero_lt_iff.mpr (by simpa [ht] using hx0)
  have ht1 : t < 1 := by
    have := (h ϖ).mpr h1
    rw [htl] at this
    exact (pow_lt_one_iff hl0).mp this
  have hinj : Function.Injective fun n : ℤ => t ^ n := zpow_right_injective₀ ht0 ht1.ne
  have hval : ∀ (a : E) (i : ℕ), algebraMap E Ω a * x ^ i ≠ 0 →
      ∃ m : ℤ, A.valuation (algebraMap E Ω a * x ^ i) = t ^ ((i : ℤ) + l * m) := by
    intro a i ha
    have ha0 : a ≠ 0 := by rintro rfl; simp at ha
    obtain ⟨m, hm⟩ := exists_val_eq_zpow h h1 h2 ha0
    refine ⟨m, ?_⟩
    rw [map_mul, hm, htl, map_pow, zpow_add₀ ht0.ne', zpow_mul, zpow_natCast, zpow_natCast, mul_comm]
  have hmod : ∀ (i j : ℕ) (m n : ℤ), i < l → j < l → t ^ ((i : ℤ) + l * m) = t ^ ((j : ℤ) + l * n) →
      i = j := by
    intro i j m n hi hj he
    have := congrArg (· % (l : ℤ)) (hinj he)
    simp only [Int.add_mul_emod_self_left] at this
    rw [Int.emod_eq_of_lt (by omega) (by omega), Int.emod_eq_of_lt (by omega) (by omega)] at this
    omega
  constructor
  · intro hb
    obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp hb
    obtain ⟨m, hm⟩ := hval a 0 (by simpa [ha] using hx0)
    have := hmod 0 1 m 0 (by omega) (by omega) (by rw [← hm]; simp [ha, ht])
    omega
  intro g b hb hb1
  have halg : IsAlgebraic E x := Algebra.IsAlgebraic.isAlgebraic x
  have hb' : b ∈ Algebra.adjoin E {x} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg]; exact hb
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hb'
  obtain ⟨p₀, rfl⟩ := hb'
  have hq : (X ^ l - C (ϖ : E)).Monic := monic_X_pow_sub_C _ hl0
  set p := p₀ %ₘ (X ^ l - C (ϖ : E))
  have hp : aeval x p = aeval x p₀ := aeval_modByMonic_eq_self_of_root (by simp [hx])
  have hdeg : p.natDegree < l := by
    have := natDegree_modByMonic_lt p₀ hq (by
      intro h1
      have := congrArg natDegree h1
      rw [natDegree_X_pow_sub_C, natDegree_one] at this
      exact hl0 this)
    rwa [natDegree_X_pow_sub_C] at this
  change A.valuation (aeval x p₀) ≤ 1 at hb1
  change A.valuation (g (aeval x p₀) - aeval x p₀) < 1
  rw [← hp, aeval_eq_sum_range' hdeg] at hb1 ⊢
  simp only [Algebra.smul_def] at hb1 ⊢
  have hle := val_term_le_one _ _ (fun i hi j hj h0 he => by
    obtain ⟨m, hm⟩ := hval _ i h0
    obtain ⟨n, hn⟩ := hval (p.coeff j) j (by
      intro h00
      rw [h00, map_zero] at he
      exact h0 (by simpa using he))
    exact hmod i j m n (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) (by rw [← hm, ← hn, he])) hb1
  have hgx : A.valuation (g x) = t := by
    refine pow_left_injective hl0 ?_
    show _ ^ l = t ^ l
    rw [← map_pow, ← map_pow, hx, g.commutes, htl]
  rw [map_sum, ← Finset.sum_sub_distrib]
  refine Valuation.map_sum_lt _ one_ne_zero fun i hi => ?_
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simp
  have hlt : A.valuation (algebraMap E Ω (p.coeff i) * x ^ i) < 1 := by
    refine lt_of_le_of_ne (hle i hi) fun he => ?_
    obtain ⟨m, hm⟩ := hval (p.coeff i) i (by intro h0; simp [h0] at he)
    have := hmod i 0 m 0 (Finset.mem_range.mp hi) (by omega) (by rw [← hm, he]; simp)
    omega
  refine Valuation.map_sub_lt _ ?_ hlt
  rw [map_mul g, g.commutes, map_pow g, map_mul, map_pow, hgx]
  rwa [map_mul, map_pow] at hlt
end GlobalTheory.InertiaMovesRoot
