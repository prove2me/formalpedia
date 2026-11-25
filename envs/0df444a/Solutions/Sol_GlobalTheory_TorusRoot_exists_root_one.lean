-- Prove2me | solution 1 for GlobalTheory.TorusRoot.exists_root_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:14:19.176336+00:00
-- url     : https://prove2.me/submissions/a9e5bb52-b726-4d43-9b0e-08dcb1ea65d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsPthRootTorusPointNilpotentAugmentedExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.TorusRoot
namespace GlobalTheory.TorusRoot
theorem _root_.solution (Ω : Type) [Field Ω] (p : ℕ) [hp : Fact p.Prime] [CharP Ω p]
    (A : Type) [CommRing A] [Algebra Ω A] (π : A →ₐ[Ω] Ω) (hπ : IsNilpotent (RingHom.ker π))
    (a : Aˣ) (ha : π a.val = 1) :
    ∃ (A' : Type) (_ : CommRing A') (_ : Algebra Ω A') (f : A →ₐ[Ω] A') (π' : A' →ₐ[Ω] Ω)
      (s : A'ˣ), Function.Injective f ∧ π'.comp f = π ∧ IsNilpotent (RingHom.ker π') ∧
      π' s.val = 1 ∧ s ^ p = Units.map (f : A →* A') a := by
  have hp0 : p ≠ 0 := hp.out.ne_zero
  haveI : Nontrivial A := π.toRingHom.domain_nontrivial
  let P : A[X] := X ^ p - C a.val
  have hP : P.Monic := monic_X_pow_sub_C _ hp0
  let f : A →ₐ[Ω] AdjoinRoot P := IsScalarTower.toAlgHom Ω A (AdjoinRoot P)
  have hf : ∀ x, f x = AdjoinRoot.of P x := fun x => rfl
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    rw [hf, ← AdjoinRoot.mk_C, AdjoinRoot.mk_eq_zero] at hx
    by_contra hx0
    refine hP.not_dvd_of_degree_lt (C_ne_zero.2 hx0) ?_ hx
    rw [degree_C hx0, degree_X_pow_sub_C (Nat.pos_of_ne_zero hp0)]
    exact_mod_cast Nat.pos_of_ne_zero hp0
  have hev : P.eval₂ (π : A →+* Ω) 1 = 0 := by
    simp [P, eval₂_sub, ha]
  let g : AdjoinRoot P →+* Ω := AdjoinRoot.lift (π : A →+* Ω) 1 hev
  have hg : ∀ x, g (f x) = π x := fun x => by
    rw [hf]; exact AdjoinRoot.lift_of hev
  have hgr : g (AdjoinRoot.root P) = 1 := AdjoinRoot.lift_root hev
  let π' : AdjoinRoot P →ₐ[Ω] Ω :=
    { g with
      commutes' := fun c => by
        have : algebraMap Ω (AdjoinRoot P) c = f (algebraMap Ω A c) := (f.commutes c).symm
        change g _ = _
        rw [this, hg, π.commutes] }
  have hroot : AdjoinRoot.root P ^ p = f a.val := by
    have h := AdjoinRoot.eval₂_root P
    simp only [P, eval₂_sub, eval₂_X_pow, eval₂_C] at h
    exact sub_eq_zero.1 h
  have hu : IsUnit (AdjoinRoot.root P) := by
    rw [← isUnit_pow_iff hp0, hroot]
    exact a.isUnit.map f
  haveI : Nontrivial (AdjoinRoot P) := g.domain_nontrivial
  haveI : CharP (AdjoinRoot P) p :=
    charP_of_injective_algebraMap (algebraMap Ω (AdjoinRoot P)).injective p
  refine ⟨AdjoinRoot P, inferInstance, inferInstance, f, π', hu.unit, hinj, ?_, ?_, hgr, ?_⟩
  · ext x; exact hg x
  · set I : Ideal (AdjoinRoot P) := (RingHom.ker π).map f with hI
    have hIn : IsNilpotent I := by
      obtain ⟨n, hn⟩ := hπ
      refine ⟨n, ?_⟩
      rw [hI, ← Ideal.map_pow, hn]
      exact Ideal.map_bot
    set J : Ideal (AdjoinRoot P) := Ideal.span {AdjoinRoot.root P - 1} with hJ
    have hJn : IsNilpotent J := by
      obtain ⟨n, hn⟩ := hIn
      refine ⟨p * n, ?_⟩
      rw [pow_mul, Ideal.zero_eq_bot, eq_bot_iff, ← Ideal.zero_eq_bot, ← hn]
      apply Ideal.pow_right_mono
      rw [hJ, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem, sub_pow_char, hroot,
        one_pow, ← map_one f, ← map_sub]
      apply Ideal.mem_map_of_mem
      rw [RingHom.mem_ker, map_sub, ha, map_one, sub_self]
    obtain ⟨n, hn⟩ := (Commute.all I J).isNilpotent_add hIn hJn
    refine ⟨n, ?_⟩
    rw [Ideal.zero_eq_bot, eq_bot_iff, ← Ideal.zero_eq_bot, ← hn]
    apply Ideal.pow_right_mono
    intro x hx
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective x
    obtain ⟨r, hr⟩ : (X - C 1 : A[X]) ∣ q - C (q.eval 1) := X_sub_C_dvd_sub_C_eval
    have h1 : AdjoinRoot.mk P q = f (q.eval 1) + (AdjoinRoot.root P - 1) * AdjoinRoot.mk P r := by
      have := congrArg (AdjoinRoot.mk P) hr
      simp only [map_sub, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X, map_one] at this
      rw [hf, ← this]; ring
    have hx' : g (AdjoinRoot.mk P q) = 0 := hx
    rw [h1, map_add, map_mul, map_sub, hgr, map_one, sub_self, zero_mul, add_zero, hg] at hx'
    rw [h1, Ideal.add_eq_sup]
    exact Submodule.add_mem_sup (Ideal.mem_map_of_mem _ hx')
      (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  · ext
    simpa using hroot
end GlobalTheory.TorusRoot
