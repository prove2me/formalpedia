-- Prove2me | solution 1 for GlobalTheory.SW.FourierJ.tsum_level_eq_sum_cosets
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:26:01.29456+00:00
-- url     : https://prove2.me/submissions/a6ffff58-bd5d-4d90-84e9-198b28a6bd9c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EchEqOneIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TsumSchwartzBruhatLevelEqSumResidueCosets
import Theorems.Thm_GlobalTheory_SW_FourierJ_intM_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Complex GlobalTheory.SW GlobalTheory.SW.FourierJ
open scoped ComplexConjugate Real
namespace GlobalTheory.SW.FourierJ
open Matrix Complex in
open scoped ComplexConjugate Real in
private theorem rep_eq_of_neg_rep_add_rep_eq_smul_zm {κ ι : Type} {R : ℕ} (hR : 0 < R)
    {n n' : κ → ι → Fin (R * R)} (m : κ → ι → ℤ)
    (hm : -_root_.GlobalTheory.SW.FourierJ.rep R n + _root_.GlobalTheory.SW.FourierJ.rep R n' =
      R • _root_.GlobalTheory.SW.FourierJ.zm m) : n = n' := by
    funext k i
    have hk := congrFun (congrFun hm k) i
    simp only [_root_.GlobalTheory.SW.FourierJ.rep, Matrix.add_apply, Matrix.neg_apply,
      Matrix.of_apply, Matrix.smul_apply, _root_.GlobalTheory.SW.FourierJ.zm, nsmul_eq_mul] at hk
    have hRq : (R : ℚ) ≠ 0 := by positivity
    rw [neg_add_eq_sub, ← sub_div, div_eq_iff hRq] at hk
    have hzq : ((n' k i : ℕ) : ℚ) - (n k i : ℕ) = (R : ℚ) * R * m k i := by
      linear_combination hk
    have hz : ((n' k i : ℕ) : ℤ) - (n k i : ℕ) = (R : ℤ) * R * m k i := by
      exact_mod_cast hzq
    have hb : ((n' k i : ℕ) : ℤ) < (R : ℤ) * R := by exact_mod_cast (n' k i).isLt
    have ha : ((n k i : ℕ) : ℤ) < (R : ℤ) * R := by exact_mod_cast (n k i).isLt
    have h0 : ((n' k i : ℕ) : ℤ) - (n k i : ℕ) = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd ⟨m k i, hz⟩
      rw [abs_lt]
      constructor <;>
        linarith [Int.natCast_nonneg (n k i : ℕ), Int.natCast_nonneg (n' k i : ℕ)]
    exact Fin.ext (by omega)
open Matrix Complex in
open scoped ComplexConjugate Real in
private theorem exists_rep_add_natCast_smul_zm_of_intM_smul {κ ι : Type} [Fintype κ] [Fintype ι] {R : ℕ}
    (hR : 0 < R) (x : Matrix κ ι ℚ) (hx : _root_.GlobalTheory.SW.IntM (R • x)) :
    ∃ (n : κ → ι → Fin (R * R)) (m : κ → ι → ℤ),
      x = _root_.GlobalTheory.SW.FourierJ.rep R n + R • _root_.GlobalTheory.SW.FourierJ.zm m := by
  obtain ⟨M, hM⟩ := (_root_.GlobalTheory.SW.FourierJ.intM_iff _).mp hx
  have hRR : (0 : ℤ) < (R : ℤ) * R := by positivity
  have hRq : (R : ℚ) ≠ 0 := by positivity
  refine ⟨fun k i => ⟨(M k i % ((R : ℤ) * R)).toNat, ?_⟩, fun k i => M k i / ((R : ℤ) * R), ?_⟩
  · have h1 := Int.emod_nonneg (M k i) hRR.ne'
    have h2 := Int.emod_lt_of_pos (M k i) hRR
    have h3 : ((M k i % ((R : ℤ) * R)).toNat : ℤ) < (R : ℤ) * R := by
      rw [Int.toNat_of_nonneg h1]; exact h2
    exact_mod_cast h3
  · ext k i
    have hk := congrFun (congrFun hM k) i
    simp only [Matrix.smul_apply, _root_.GlobalTheory.SW.FourierJ.zm, Matrix.of_apply, nsmul_eq_mul] at hk
    simp only [_root_.GlobalTheory.SW.FourierJ.rep, Matrix.add_apply, Matrix.smul_apply,
      Matrix.of_apply, _root_.GlobalTheory.SW.FourierJ.zm, nsmul_eq_mul]
    have h1 := Int.emod_nonneg (M k i) hRR.ne'
    have hn : (((M k i % ((R : ℤ) * R)).toNat : ℕ) : ℚ) = ((M k i % ((R : ℤ) * R) : ℤ) : ℚ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h1]
    have hq : ((M k i % ((R : ℤ) * R) : ℤ) : ℚ) + (R : ℚ) * R * ((M k i / ((R : ℤ) * R) : ℤ) : ℚ)
        = (M k i : ℚ) := by
      have := Int.mul_ediv_add_emod (M k i) ((R : ℤ) * R)
      have h' : (R : ℚ) * R * ((M k i / ((R : ℤ) * R) : ℤ) : ℚ) +
          ((M k i % ((R : ℤ) * R) : ℤ) : ℚ) = (M k i : ℚ) := by
        exact_mod_cast this
      linear_combination h'
    have hx' : x k i = (M k i : ℚ) / R := by
      rw [eq_div_iff hRq]
      linear_combination hk
    rw [hx', hn, ← hq, add_div]
    congr 1
    rw [mul_assoc, mul_div_cancel_left₀ _ hRq]
end GlobalTheory.SW.FourierJ
end

set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.SW.FourierJ
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.FourierJ
open Matrix Complex
open scoped ComplexConjugate Real
namespace GlobalTheory.SW.FourierJ
namespace _root_.GlobalTheory.SW.FourierJ
theorem _root_.solution : ∀ (κ ι : Type) [Fintype κ] [Fintype ι]
    [DecidableEq κ]
    [DecidableEq ι] (R : ℕ) (φ F : Matrix κ ι ℚ → ℂ), 0 < R → _root_.GlobalTheory.SW.HasLevel R φ →
    Summable (fun x => φ x * F x) → ∑' x, φ x * F x =
      ∑ n : κ → ι → Fin (R * R), φ (_root_.GlobalTheory.SW.FourierJ.rep R n) *
        ∑' m : κ → ι → ℤ, F (_root_.GlobalTheory.SW.FourierJ.rep R n +
          (R : ℚ) • _root_.GlobalTheory.SW.FourierJ.zm m) := by
  intro κ ι _ _ _ _ R φ F hR hφ hsum
  have hRq : (R : ℚ) ≠ 0 := by positivity
  have hsmul : ∀ m : κ → ι → ℤ, (R : ℚ) • _root_.GlobalTheory.SW.FourierJ.zm m = R • _root_.GlobalTheory.SW.FourierJ.zm m :=
    fun m => Nat.cast_smul_eq_nsmul ℚ R _
  let e : (κ → ι → Fin (R * R)) × (κ → ι → ℤ) → Matrix κ ι ℚ := fun p =>
    _root_.GlobalTheory.SW.FourierJ.rep R p.1 + (R : ℚ) • _root_.GlobalTheory.SW.FourierJ.zm p.2
  have he : Function.Injective e := by
    rintro ⟨n, m⟩ ⟨n', m'⟩ h
    simp only [e] at h
    have hn : n = n' := by
      apply rep_eq_of_neg_rep_add_rep_eq_smul_zm hR (m - m')
      ext k i
      have hk := congrFun (congrFun h k) i
      simp only [_root_.GlobalTheory.SW.FourierJ.rep, Matrix.add_apply, Matrix.neg_apply,
        Matrix.of_apply, Matrix.smul_apply, _root_.GlobalTheory.SW.FourierJ.zm, nsmul_eq_mul, smul_eq_mul,
        Pi.sub_apply] at hk ⊢
      push_cast
      linear_combination -hk
    subst hn
    have hm : m = m' := by
      funext k i
      have hk := congrFun (congrFun h k) i
      simp only [Matrix.add_apply, Matrix.smul_apply, _root_.GlobalTheory.SW.FourierJ.zm, Matrix.of_apply,
        smul_eq_mul, add_right_inj] at hk
      exact_mod_cast mul_left_cancel₀ hRq hk
    rw [hm]
  have hsupp : Function.support (fun x => φ x * F x) ⊆ Set.range e := by
    intro x hx
    have hφx : φ x ≠ 0 := left_ne_zero_of_mul (Function.mem_support.mp hx)
    obtain ⟨n, m, hnm⟩ := exists_rep_add_natCast_smul_zm_of_intM_smul hR x (hφ.1 x hφx)
    exact ⟨(n, m), by simp only [e, hsmul]; exact hnm.symm⟩
  rw [← he.tsum_eq hsupp]
  have hs2 : Summable fun p => φ (e p) * F (e p) := hsum.comp_injective he
  rw [hs2.tsum_prod' (fun n => hs2.comp_injective (by intro m m' h; simpa using h)),
    tsum_fintype]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← tsum_mul_left]
  refine tsum_congr fun m => ?_
  simp only [e]
  rw [hφ.2 _ _ ((_root_.GlobalTheory.SW.FourierJ.intM_iff _).mpr ⟨m, rfl⟩)]
end _root_.GlobalTheory.SW.FourierJ
end GlobalTheory.SW.FourierJ
