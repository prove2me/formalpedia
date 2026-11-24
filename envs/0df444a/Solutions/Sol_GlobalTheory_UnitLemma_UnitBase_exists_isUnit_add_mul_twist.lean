-- Prove2me | solution 1 for GlobalTheory.UnitLemma.UnitBase.exists_isUnit_add_mul_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:01:47.322885+00:00
-- url     : https://prove2.me/submissions/bd15d4f5-dfba-4604-a5fb-1764cdfca479

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitBasePointAdjoinTwistedSigma

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.UnitBase
open GlobalTheory.UnitLemma Polynomial
namespace GlobalTheory.UnitLemma.UnitBase
theorem _root_.solution {R : Type} [CommRing R] (τ : R ≃+* R) (hτ : ∀ y, τ (τ y) = y)
    (a : R) (ha : IsUnit a) (hfin : {M : Ideal R | M.IsMaximal}.Finite)
    (x : R) (hx : IsUnit (τ x - x)) : ∃ y : R, IsUnit (y + a * τ y) := by
  classical
  haveI : Finite {M : Ideal R // M.IsMaximal} := hfin.to_subtype
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin {M : Ideal R // M.IsMaximal}
  let pt : {M : Ideal R // M.IsMaximal} → {M : Ideal R // M.IsMaximal} := fun M =>
    ⟨M.1.comap (τ : R →+* R), by haveI := M.2; exact Ideal.comap_isMaximal_of_surjective _ τ.surjective⟩
  have mem_pt : ∀ M z, z ∈ (pt M).1 ↔ τ z ∈ M.1 := fun M z => Iff.rfl
  have pt_pt : ∀ M, pt (pt M) = M := by
    intro M; apply Subtype.ext; ext z; rw [mem_pt, mem_pt, hτ]
  let t : {M : Ideal R // M.IsMaximal} → R := fun M =>
    if pt M = M then (if 1 + a ∈ M.1 then x else 1) else if e M < e (pt M) then 1 else 0
  have hcop : Pairwise (Function.onFun IsCoprime fun M : {M : Ideal R // M.IsMaximal} => M.1) := by
    intro M N hne
    haveI := M.2; haveI := N.2
    exact Ideal.isCoprime_of_isMaximal (fun h => hne (Subtype.ext h))
  obtain ⟨q, hq⟩ := Ideal.quotientInfToPiQuotient_surj hcop (fun M => Ideal.Quotient.mk M.1 (t M))
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hy : ∀ M : {M : Ideal R // M.IsMaximal}, y - t M ∈ M.1 := by
    intro M
    have := congrFun hq M
    rw [Ideal.quotientInfToPiQuotient_mk'] at this
    exact Ideal.Quotient.eq.1 this
  refine ⟨y, ?_⟩
  by_contra hnu
  obtain ⟨M0, hM0, hyM⟩ := exists_max_ideal_of_mem_nonunits hnu
  set M : {M : Ideal R // M.IsMaximal} := ⟨M0, hM0⟩ with hMdef
  have hyM' : y + a * τ y ∈ M.1 := hyM
  have hne1 : (1 : R) ∉ M.1 := fun h => hM0.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hunit : ∀ {u : R}, IsUnit u → u ∉ M.1 := fun hu h => hM0.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
  by_cases hfix : pt M = M
  · have hτM : ∀ z, z ∈ M.1 → τ z ∈ M.1 := by
      intro z hz; rw [← mem_pt, hfix]; exact hz
    have hd := hy M
    have ht : t M + a * τ (t M) ∈ M.1 := by
      have : t M + a * τ (t M) = (y + a * τ y) - (y - t M) - a * τ (y - t M) := by
        rw [map_sub]; ring
      rw [this]
      exact M.1.sub_mem (M.1.sub_mem hyM' hd) (M.1.mul_mem_left _ (hτM _ hd))
    by_cases h1a : 1 + a ∈ M.1
    · have htx : t M = x := by simp only [t, if_pos hfix, if_pos h1a]
      rw [htx] at ht
      have : a * (τ x - x) ∈ M.1 := by
        have : a * (τ x - x) = (x + a * τ x) - x * (1 + a) := by ring
        rw [this]; exact M.1.sub_mem ht (M.1.mul_mem_left _ h1a)
      exact hunit (ha.mul hx) this
    · have ht1 : t M = 1 := by simp only [t, if_pos hfix, if_neg h1a]
      rw [ht1, map_one, mul_one, add_comm] at ht
      exact h1a (by rwa [add_comm])
  · have hfix' : pt (pt M) ≠ pt M := by rw [pt_pt]; exact Ne.symm hfix
    by_cases hlt : e M < e (pt M)
    · have ht1 : t M = 1 := by simp only [t, if_neg hfix, if_pos hlt]
      have hlt' : ¬ e (pt M) < e (pt (pt M)) := by rw [pt_pt]; exact not_lt.2 hlt.le
      have ht0 : t (pt M) = 0 := by simp only [t, if_neg hfix', if_neg hlt']
      have h1 := hy M
      have h2 := hy (pt M)
      rw [ht1] at h1
      rw [ht0, sub_zero, mem_pt] at h2
      have : (1 : R) = (y + a * τ y) - (y - 1) - a * τ y := by ring
      exact hne1 (this ▸ M.1.sub_mem (M.1.sub_mem hyM' h1) (M.1.mul_mem_left _ h2))
    · have ht0 : t M = 0 := by simp only [t, if_neg hfix, if_neg hlt]
      have hne : e (pt M) ≠ e M := fun h => hfix (e.injective h)
      have hlt' : e (pt M) < e (pt (pt M)) := by
        rw [pt_pt]; exact lt_of_le_of_ne (not_lt.1 hlt) hne
      have ht1 : t (pt M) = 1 := by simp only [t, if_neg hfix', if_pos hlt']
      have h1 := hy M
      have h2 := hy (pt M)
      rw [ht0, sub_zero] at h1
      rw [ht1, mem_pt, map_sub, map_one] at h2
      have : a = (y + a * τ y) - y - a * (τ y - 1) := by ring
      exact hunit ha (this ▸ M.1.sub_mem (M.1.sub_mem hyM' h1) (M.1.mul_mem_left _ h2))
end GlobalTheory.UnitLemma.UnitBase
