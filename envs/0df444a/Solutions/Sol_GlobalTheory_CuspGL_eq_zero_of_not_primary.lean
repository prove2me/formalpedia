-- Prove2me | solution 1 for GlobalTheory.CuspGL.eq_zero_of_not_primary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:42:45.881793+00:00
-- url     : https://prove2.me/submissions/a186a656-f8df-4616-b3ee-124c24c8f3bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsConjEqAddOfIsCoprime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimary
import Theorems.Thm_GlobalTheory_CuspGL_irreducible_dvd_of_dvd_charpoly_of_aeval_eq_zero
import Theorems.Thm_GlobalTheory_CuspGL_exists_conj_eq_add_of_isCoprime
import Theorems.Thm_GlobalTheory_CuspGL_intertwine_aeval_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (φ : Module.End F V → ℂ), IsClassFn φ → IsPrimitive φ → 0 < Module.finrank F V →
    ∀ g : Module.End F V, (¬ ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧
      LinearMap.charpoly g = f ^ m) → φ g = 0 := by
  intro F _ _ V _ _ _ φ hcl hpr hdim g hg
  have hmon : (LinearMap.charpoly g).Monic := LinearMap.charpoly_monic g
  have hne0 : LinearMap.charpoly g ≠ 0 := hmon.ne_zero
  have hnu : ¬ IsUnit (LinearMap.charpoly g) := by
    intro hu
    have h := LinearMap.charpoly_natDegree g
    rw [Polynomial.natDegree_eq_zero_of_isUnit hu] at h
    omega
  obtain ⟨f, hfm, hf, hfd⟩ := Polynomial.exists_monic_irreducible_factor _ hnu
  obtain ⟨m, Q, hnd, hfac⟩ := WfDvdMonoid.max_power_factor hne0 hf
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, pow_zero, one_mul] at hfac
      exact absurd (hfac ▸ hfd) hnd
    · exact h
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hfac
    exact hne0 hfac
  have hQ : ¬ IsUnit Q := by
    intro hu
    have hQm : Q.Monic := (hfm.pow m).of_mul_monic_left (hfac ▸ hmon)
    have h1 : Q = 1 := hQm.eq_one_of_isUnit hu
    exact hg ⟨f, m, hfm, hf, hm, by rw [hfac, h1, mul_one]⟩
  have hcop : IsCoprime (f ^ m) Q := ((hf.coprime_iff_not_dvd).mpr hnd).pow_left
  have hPQ : aeval g (f ^ m) * aeval g Q = 0 := by
    rw [← map_mul, ← hfac, LinearMap.aeval_self_charpoly]
  have hgA : ∀ x ∈ LinearMap.ker (aeval g (f ^ m)), g x ∈ LinearMap.ker (aeval g (f ^ m)) := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    have hc : aeval g (f ^ m) * g = g * aeval g (f ^ m) := by
      calc aeval g (f ^ m) * g = aeval g (f ^ m * X) := by rw [map_mul, aeval_X]
        _ = aeval g (X * f ^ m) := by rw [mul_comm]
        _ = g * aeval g (f ^ m) := by rw [map_mul, aeval_X]
    have h := congrArg (fun u : Module.End F V => u x) hc
    simp only [Module.End.mul_apply] at h
    rw [h, hx, map_zero]
  set A := LinearMap.ker (aeval g (f ^ m)) with hAdef
  have hPA : aeval (g.restrict hgA) (f ^ m) = 0 := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    have h := intertwine_aeval_apply A.subtype (g.restrict hgA) g (fun _ => rfl) (f ^ m) x
    rw [Submodule.subtype_apply, Submodule.subtype_apply] at h
    rw [h, LinearMap.zero_apply, Submodule.coe_zero]
    exact LinearMap.mem_ker.mp x.2
  have hQq : aeval (A.mapQ A g (fun x hx => hgA x hx)) Q = 0 := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := A.mkQ_surjective y
    have h := intertwine_aeval_apply A.mkQ g (A.mapQ A g (fun x hx => hgA x hx)) (fun _ => rfl) Q x
    rw [← h, LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      hAdef, LinearMap.mem_ker, ← Module.End.mul_apply, hPQ, LinearMap.zero_apply]
  have hcp : IsCoprime (LinearMap.charpoly (g.restrict hgA))
      (LinearMap.charpoly (A.mapQ A g (fun x hx => hgA x hx))) := by
    refine isCoprime_of_irreducible_dvd (fun h => (LinearMap.charpoly_monic _).ne_zero h.1) ?_
    intro z hz hzA hzQ
    have h1 : z ∣ f ^ m :=
      irreducible_dvd_of_dvd_charpoly_of_aeval_eq_zero (g.restrict hgA) z (f ^ m) hz hzA hPA
    have h2 : z ∣ Q := irreducible_dvd_of_dvd_charpoly_of_aeval_eq_zero _ z Q hz hzQ hQq
    exact hz.not_isUnit (hcop.isUnit_of_dvd' h1 h2)
  have hAbot : A ≠ ⊥ := by
    intro hA
    have hsup := Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime g hcop
    rw [← hAdef, hA, bot_sup_eq, ← hfac, LinearMap.aeval_self_charpoly, LinearMap.ker_zero] at hsup
    have hQ0' : aeval g Q = 0 := LinearMap.ker_eq_top.mp hsup
    exact hnd (irreducible_dvd_of_dvd_charpoly_of_aeval_eq_zero g f Q hf hfd hQ0')
  have hAtop : A ≠ ⊤ := by
    intro hA
    have hP0 : aeval g (f ^ m) = 0 := LinearMap.ker_eq_top.mp hA
    obtain ⟨z, hz, hzQ⟩ := WfDvdMonoid.exists_irreducible_factor hQ hQ0
    have hzc : z ∣ LinearMap.charpoly g := hzQ.trans ⟨f ^ m, by rw [hfac, mul_comm]⟩
    have h1 : z ∣ f ^ m := irreducible_dvd_of_dvd_charpoly_of_aeval_eq_zero g z (f ^ m) hz hzc hP0
    exact hz.not_isUnit (hcop.isUnit_of_dvd' h1 hzQ)
  have hconj := exists_conj_eq_add_of_isCoprime F V A g hgA hcp
  have hsum := hpr A hAbot hAtop g hgA
  have hconst : ∀ h ∈ nilRad A, φ (g + h) = φ g := by
    intro h hh
    obtain ⟨e, he⟩ := hconj h hh
    rw [← he, hcl]
  rw [finsum_mem_congr rfl hconst] at hsum
  have : Finite V := Module.finite_of_finite F
  have : Finite (Module.End F V) :=
    Finite.of_injective (fun u : Module.End F V => (u : V → V)) DFunLike.coe_injective
  have hfin : (nilRad A).Finite := Set.toFinite _
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_const, nsmul_eq_mul] at hsum
  have h0 : (0 : Module.End F V) ∈ nilRad A := ⟨fun _ => A.zero_mem, fun _ _ => rfl⟩
  have hcard : (hfin.toFinset.card : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨0, hfin.mem_toFinset.mpr h0⟩)
  exact (mul_eq_zero.mp hsum).resolve_left hcard
end GlobalTheory.CuspGL
