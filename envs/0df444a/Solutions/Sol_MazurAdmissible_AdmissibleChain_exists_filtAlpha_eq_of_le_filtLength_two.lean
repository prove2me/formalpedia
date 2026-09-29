-- Prove2me | solution 1 for MazurAdmissible.AdmissibleChain.exists_filtAlpha_eq_of_le_filtLength_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/7d3c6b44-ce77-515e-ab59-aaf8b906689f

import Definitions.Def_MazurAdmissible_GaloisModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MazurAdmissible_AdmissibleChain_exists_filtAlpha_eq_of_le_filtLength_two

p2m_open "MazurAdmissible P2MW.S_MazurAdmissible_AdmissibleChain_exists_filtAlpha_eq_of_le_filtLength_two.MazurAdmissible"

namespace MazurAdmissible p2m_export "MazurAdmissible" "OpenAction IsTrivialStep IsCyclotomicStep AdmissibleChain filtAlpha filtLength" namespace AdmissibleChain p2m_export "MazurAdmissible.AdmissibleChain" "tag hmono step n mk hact htop hbot hcard" end MazurAdmissible.AdmissibleChain
namespace MazurAdmissible.AdmissibleChain
p2m_open_scoped "MazurAdmissible MazurAdmissible.AdmissibleChain" in

private theorem _root_.MazurAdmissible.AdmissibleChain.isTrivialStep_of_two
    {M : Type*} [AddCommGroup M] {Φ : OpenAction M} (c : AdmissibleChain 2 Φ) (i : Fin c.n) :
    IsTrivialStep Φ (c.step i.castSucc) (c.step i.succ) := by
  have h := c.hact i
  by_cases ht : c.tag i = true
  · simpa [ht] using h
  · simp only [ht] at h
    intro σ x hx
    have hprim : IsPrimitiveRoot (-1 : AlgebraicClosure ℚ) 2 :=
      IsPrimitiveRoot.neg_one 0 (by norm_num)
    have h1 : σ (-1 : AlgebraicClosure ℚ) = (-1) ^ (1 : ℕ) := by simp
    simpa using h σ (-1) hprim 1 h1 x hx

end MazurAdmissible.AdmissibleChain
p2m_export "" "MazurAdmissible.AdmissibleChain.isTrivialStep_of_two"
namespace MazurAdmissible.AdmissibleChain
p2m_open_scoped "MazurAdmissible MazurAdmissible.AdmissibleChain" in

private theorem _root_.MazurAdmissible.AdmissibleChain.two_nsmul_mem_of_two
    {M : Type*} [AddCommGroup M] {Φ : OpenAction M} (c : AdmissibleChain 2 Φ) (i : Fin c.n)
    (x : M) (hx : x ∈ c.step i.succ) : (2 : ℕ) • x ∈ c.step i.castSucc := by
  have hq : (2 : ℕ) • (QuotientAddGroup.mk (s := (c.step i.castSucc).addSubgroupOf (c.step i.succ))
      (⟨x, hx⟩ : ↥(c.step i.succ))) = 0 := by
    have h0 := card_nsmul_eq_zero'
      (x := QuotientAddGroup.mk (s := (c.step i.castSucc).addSubgroupOf (c.step i.succ))
        (⟨x, hx⟩ : ↥(c.step i.succ)))
    rwa [c.hcard i] at h0
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at hq
  simpa using hq

end MazurAdmissible.AdmissibleChain
p2m_export "" "MazurAdmissible.AdmissibleChain.two_nsmul_mem_of_two"
namespace MazurAdmissible.AdmissibleChain
p2m_open_scoped "MazurAdmissible MazurAdmissible.AdmissibleChain" in

private theorem _root_.MazurAdmissible.AdmissibleChain.isCyclotomicStep_of_two
    {M : Type*} [AddCommGroup M] {Φ : OpenAction M} (c : AdmissibleChain 2 Φ) (i : Fin c.n) :
    IsCyclotomicStep 2 Φ (c.step i.castSucc) (c.step i.succ) := by
  intro σ ζ hζ a ha x hx
  have hζ1 : ζ = -1 := hζ.eq_neg_one_of_two_right
  subst hζ1
  rw [map_neg, map_one] at ha
  have hodd : Odd a := (neg_one_pow_eq_neg_one_iff_odd (R := AlgebraicClosure ℚ) (by norm_num)).mp ha.symm
  obtain ⟨j, rfl⟩ := hodd
  have htriv := c.isTrivialStep_of_two i σ x hx
  have h2 := c.two_nsmul_mem_of_two i x hx
  have : Φ.φ σ x - (2 * j + 1) • x = (Φ.φ σ x - x) - j • ((2 : ℕ) • x) := by
    rw [add_smul, one_smul, mul_comm, mul_smul]
    abel
  rw [this]
  exact sub_mem htriv (AddSubgroup.nsmul_mem _ h2 j)

end MazurAdmissible.AdmissibleChain
p2m_export "" "MazurAdmissible.AdmissibleChain.isCyclotomicStep_of_two"
p2m_open_scoped "MazurAdmissible MazurAdmissible.AdmissibleChain" in

theorem MazurAdmissible.AdmissibleChain.exists_filtAlpha_eq_of_le_filtLength_two
    {M : Type*} [AddCommGroup M] (Φ : OpenAction M) (c : AdmissibleChain 2 Φ)
    (k : ℕ) (hk : k ≤ filtLength c) :
    ∃ c' : AdmissibleChain 2 Φ, filtLength c' = filtLength c ∧ filtAlpha c' = k := by
  refine ⟨{ n := c.n, step := c.step, hbot := c.hbot, htop := c.htop, hmono := c.hmono,
            tag := fun i => decide (i.val < k), hcard := c.hcard, hact := ?_ }, rfl, ?_⟩
  · intro i
    by_cases hi : i.val < k
    · simp only [hi, decide_true, ↓reduceIte]
      exact c.isTrivialStep_of_two i
    · simp only [hi, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact c.isCyclotomicStep_of_two i
  ·
    change (Finset.univ.filter fun i : Fin c.n => decide (i.val < k) = true).card = k
    have hk' : k ≤ c.n := hk
    have : (Finset.univ.filter fun i : Fin c.n => decide (i.val < k) = true).map Fin.valEmbedding
        = Finset.range k := by
      ext j
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq,
        Fin.valEmbedding_apply, Finset.mem_range]
      constructor
      · rintro ⟨i, hi, rfl⟩; exact hi
      · intro hj; exact ⟨⟨j, lt_of_lt_of_le hj hk'⟩, hj, rfl⟩
    rw [← Finset.card_map, this, Finset.card_range]

theorem solution
    {M : Type*} [AddCommGroup M] (Φ : OpenAction M) (c : AdmissibleChain 2 Φ)
    (k : ℕ) (hk : k ≤ filtLength c) :
    ∃ c' : AdmissibleChain 2 Φ, filtLength c' = filtLength c ∧ filtAlpha c' = k :=
  MazurAdmissible.AdmissibleChain.exists_filtAlpha_eq_of_le_filtLength_two Φ c k hk

end S_MazurAdmissible_AdmissibleChain_exists_filtAlpha_eq_of_le_filtLength_two
end P2MW
export P2MW.S_MazurAdmissible_AdmissibleChain_exists_filtAlpha_eq_of_le_filtLength_two (solution)
