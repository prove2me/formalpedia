-- Prove2me | solution 1 for GlobalTheory.SW.FourierJ.haar_eq_sum_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:23:31.171353+00:00
-- url     : https://prove2.me/submissions/04ef19da-c1ca-4e7c-944a-ed00e1e2d9b1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EchEqOneIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatIntegralEqSumResidueRepresentative
import Theorems.Thm_GlobalTheory_SW_FourierJ_intM_iff
import Theorems.Thm_GlobalTheory_SW_HaarLevel_intM_iff
import Theorems.Thm_GlobalTheory_SW_HaarLevel_mem_perSub
import Theorems.Thm_GlobalTheory_SW_HaarLevel_periodic
import Theorems.Thm_GlobalTheory_SW_haar_eq_haarAt

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
private theorem exists_rep_add_smul_zm_of_intM_smul {κ ι : Type} [Fintype κ] [Fintype ι] {R : ℕ}
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
open Matrix Complex in
open scoped ComplexConjugate Real in
private theorem mem_perSub_iff_exists_eq_smul_zm {κ ι : Type} [Fintype κ] [Fintype ι] (R : ℕ)
    (y : Matrix κ ι ℚ) : y ∈ _root_.GlobalTheory.SW.perSub ℚ κ ι R ↔
      ∃ m : κ → ι → ℤ, y = R • _root_.GlobalTheory.SW.FourierJ.zm m := by
  rw [_root_.GlobalTheory.SW.HaarLevel.mem_perSub]
  constructor
  · rintro ⟨y', rfl⟩
    obtain ⟨m, hm⟩ := (_root_.GlobalTheory.SW.FourierJ.intM_iff _).mp
      ((_root_.GlobalTheory.SW.HaarLevel.intM_iff _).mpr ⟨y', rfl⟩)
    exact ⟨m, by rw [hm]⟩
  · rintro ⟨m, rfl⟩
    obtain ⟨y', hy'⟩ := (_root_.GlobalTheory.SW.HaarLevel.intM_iff _).mp
      ((_root_.GlobalTheory.SW.FourierJ.intM_iff _).mpr ⟨m, rfl⟩)
    exact ⟨y', by rw [hy']⟩
open Matrix Complex in
open scoped ComplexConjugate Real in
private theorem rep_injective_of_neg_add_eq_smul_zm {κ ι : Type} {R : ℕ} (hR : 0 < R)
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
theorem _root_.solution : ∀ (κ ι : Type) [Fintype κ]
    [Fintype ι] [DecidableEq κ] [DecidableEq ι] (R : ℕ) (φ : Matrix κ ι ℚ → ℂ), 0 < R →
    _root_.GlobalTheory.SW.HasLevel R φ → _root_.GlobalTheory.SW.haar φ =
      ((R : ℂ) ^ (Fintype.card κ * Fintype.card ι))⁻¹ *
        ∑ n : κ → ι → Fin (R * R), φ (_root_.GlobalTheory.SW.FourierJ.rep R n) := by
  intro κ ι _ _ _ _ R φ hR hφ
  classical
  obtain ⟨h1, -⟩ := _root_.GlobalTheory.SW.haar_eq_haarAt ℚ κ ι R φ hR hφ
  rw [h1]
  unfold _root_.GlobalTheory.SW.haarAt
  rw [Module.finrank_self, one_mul]
  congr 1
  have hper : ∀ x : Matrix κ ι ℚ, φ (Quotient.out
      (QuotientAddGroup.mk x : Matrix κ ι ℚ ⧸ _root_.GlobalTheory.SW.perSub ℚ κ ι R)) = φ x := by
    intro x
    have hmem : -x + Quotient.out
        (QuotientAddGroup.mk x : Matrix κ ι ℚ ⧸ _root_.GlobalTheory.SW.perSub ℚ κ ι R) ∈
        _root_.GlobalTheory.SW.perSub ℚ κ ι R :=
      QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' _).symm
    have h := _root_.GlobalTheory.SW.HaarLevel.periodic hφ x _ hmem
    rwa [add_neg_cancel_left] at h
  have hsupp : (Function.support fun q : Matrix κ ι ℚ ⧸ _root_.GlobalTheory.SW.perSub ℚ κ ι R =>
      φ (Quotient.out q)) ⊆ ↑(Finset.univ.image fun n : κ → ι → Fin (R * R) =>
        (QuotientAddGroup.mk (_root_.GlobalTheory.SW.FourierJ.rep R n) :
          Matrix κ ι ℚ ⧸ _root_.GlobalTheory.SW.perSub ℚ κ ι R)) := by
    intro q hq
    obtain ⟨n, m, hnm⟩ := exists_rep_add_smul_zm_of_intM_smul hR _ (hφ.1 _ (Function.mem_support.mp hq))
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
    refine ⟨n, ?_⟩
    rw [← QuotientAddGroup.out_eq' q, hnm, QuotientAddGroup.eq, neg_add_cancel_left]
    exact (mem_perSub_iff_exists_eq_smul_zm R _).mpr ⟨m, rfl⟩
  have hinj : Function.Injective fun n : κ → ι → Fin (R * R) =>
      (QuotientAddGroup.mk (_root_.GlobalTheory.SW.FourierJ.rep R n) :
        Matrix κ ι ℚ ⧸ _root_.GlobalTheory.SW.perSub ℚ κ ι R) := by
    intro n n' h
    obtain ⟨m, hm⟩ := (mem_perSub_iff_exists_eq_smul_zm R _).mp (QuotientAddGroup.eq.mp h)
    exact rep_injective_of_neg_add_eq_smul_zm hR m hm
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image (fun n _ n' _ h => hinj h)]
  exact Finset.sum_congr rfl fun n _ => hper _
end _root_.GlobalTheory.SW.FourierJ
end GlobalTheory.SW.FourierJ
