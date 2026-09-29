-- Prove2me | solution 1 for HenselianLocalRing.of_moduleFinite_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/09159004-4faf-5048-962e-96f5f8922bb0

import Mathlib
import Theorems.Thm_HenselianLocalRing_exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HenselianLocalRing_of_moduleFinite_of_isLocalRing

set_option autoImplicit false

universe u v

namespace HensFinAux

open IsLocalRing Polynomial

theorem main (R : Type u) [CommRing R] [HenselianLocalRing R]
    {S : Type v} [CommRing S] [IsLocalRing S] [Algebra R S] [Module.Finite R S]
    (f : S[X]) (hf : f.Monic) (a₀ : S) (h₁ : f.eval a₀ ∈ maximalIdeal S)
    (h₂ : IsUnit (f.derivative.eval a₀)) : ∃ a : S, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal S := by
  classical

  haveI : Module.Finite S (AdjoinRoot f) := Module.Finite.of_basis (AdjoinRoot.powerBasis' hf).basis
  haveI : Module.Finite R (AdjoinRoot f) := Module.Finite.trans S (AdjoinRoot f)

  have hroot : f.eval₂ (residue S) (residue S a₀) = 0 := by
    rw [Polynomial.eval₂_at_apply]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr h₁
  set φ : AdjoinRoot f →+* ResidueField S := AdjoinRoot.lift (residue S) (residue S a₀) hroot with hφ
  have hφof : ∀ s : S, φ (AdjoinRoot.of f s) = residue S s := fun s => by
    rw [hφ, AdjoinRoot.lift_of]
  have hφroot : φ (AdjoinRoot.root f) = residue S a₀ := by rw [hφ, AdjoinRoot.lift_root]
  have hφsurj : Function.Surjective φ := fun x => by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨AdjoinRoot.of f s, hφof s⟩
  haveI hm₀max : (RingHom.ker φ).IsMaximal := RingHom.ker_isMaximal_of_surjective φ hφsurj
  set m₀ : MaximalSpectrum (AdjoinRoot f) := ⟨RingHom.ker φ, hm₀max⟩ with hm₀

  obtain ⟨hfin, e, hce, hnot, -, hloc⟩ :=
    HenselianLocalRing.exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite
      (R := R) (S := AdjoinRoot f)
  set e₀ : AdjoinRoot f := e m₀ with he₀
  have he₀idem : e₀ * e₀ = e₀ := (hce.idem m₀).eq
  have he₀not : e₀ ∉ RingHom.ker φ := hnot m₀
  haveI hC₀loc : IsLocalRing (AdjoinRoot f ⧸ Ideal.span {1 - e₀}) := hloc m₀

  set J : Ideal (AdjoinRoot f) := Ideal.span {1 - e₀} with hJ
  set π : AdjoinRoot f →+* AdjoinRoot f ⧸ J := Ideal.Quotient.mk J with hπ
  set ι : S →+* AdjoinRoot f ⧸ J := π.comp (AdjoinRoot.of f) with hι
  set x₀ : AdjoinRoot f ⧸ J := π (AdjoinRoot.root f) with hx₀
  have hιalg : ∀ s : S, ι s = algebraMap S (AdjoinRoot f ⧸ J) s := fun s => rfl

  have h1e : 1 - e₀ ∈ RingHom.ker φ := by
    have hz : e₀ * (1 - e₀) = 0 := by rw [mul_sub, mul_one, he₀idem, sub_self]
    have : e₀ * (1 - e₀) ∈ RingHom.ker φ := by rw [hz]; exact Ideal.zero_mem _
    exact ((hm₀max.isPrime.mem_or_mem this).resolve_left he₀not)
  have hJle : J ≤ RingHom.ker φ := by
    rw [hJ, Ideal.span_le, Set.singleton_subset_iff]; exact h1e

  set φ₀ : AdjoinRoot f ⧸ J →+* ResidueField S := Ideal.Quotient.lift J φ (fun c hc => hJle hc) with hφ₀
  have hφ₀π : ∀ c, φ₀ (π c) = φ c := fun c => by rw [hφ₀, hπ, Ideal.Quotient.lift_mk]
  have hunit : ∀ c : AdjoinRoot f, c ∉ RingHom.ker φ → IsUnit (π c) := by
    intro c hc
    by_contra hnu
    have hmem : π c ∈ maximalIdeal (AdjoinRoot f ⧸ J) := (IsLocalRing.mem_maximalIdeal _).mpr hnu

    have hφ₀surj : Function.Surjective φ₀ := fun x => by
      obtain ⟨c, rfl⟩ := hφsurj x; exact ⟨π c, hφ₀π c⟩
    have hker : RingHom.ker φ₀ = maximalIdeal (AdjoinRoot f ⧸ J) :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective φ₀ hφ₀surj)
    rw [← hker, RingHom.mem_ker, hφ₀π] at hmem
    exact hc hmem

  set q : S[X] := f /ₘ (X - C a₀) with hq
  have hfq : f = C (f.eval a₀) + (X - C a₀) * q := by
    have := Polynomial.modByMonic_add_div f (X - C a₀)
    rw [Polynomial.modByMonic_X_sub_C_eq_C_eval] at this
    exact this.symm
  have hqa₀ : q.eval a₀ = f.derivative.eval a₀ := by
    have hd : f.derivative = q + (X - C a₀) * q.derivative := by
      conv_lhs => rw [hfq]
      rw [Polynomial.derivative_add, Polynomial.derivative_C, zero_add, Polynomial.derivative_mul,
        Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C, sub_zero, one_mul]
    rw [hd, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, sub_self, zero_mul, add_zero]

  have hqunit : IsUnit (π (AdjoinRoot.mk f q)) := by
    apply hunit
    intro hmem
    rw [RingHom.mem_ker, hφ, AdjoinRoot.lift_mk, Polynomial.eval₂_at_apply, hqa₀,
      IsLocalRing.residue_eq_zero_iff] at hmem
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem h₂

  have hfx₀ : ι (f.eval a₀) + (x₀ - ι a₀) * π (AdjoinRoot.mk f q) = 0 := by
    have h0 : AdjoinRoot.mk f f = 0 := AdjoinRoot.mk_self
    have : AdjoinRoot.mk f f = AdjoinRoot.of f (f.eval a₀) + (AdjoinRoot.root f - AdjoinRoot.of f a₀) * AdjoinRoot.mk f q := by
      have h' : AdjoinRoot.mk f (C (f.eval a₀) + (X - C a₀) * q) =
          AdjoinRoot.of f (f.eval a₀) + (AdjoinRoot.root f - AdjoinRoot.of f a₀) * AdjoinRoot.mk f q := by
        rw [map_add, map_mul, map_sub, AdjoinRoot.mk_C, AdjoinRoot.mk_X, AdjoinRoot.mk_C]
      rwa [← hfq] at h'
    rw [h0] at this
    have := congrArg π this.symm
    rwa [map_zero, map_add, map_mul, map_sub] at this
  obtain ⟨u, hu⟩ := hqunit
  have hx₀a₀ : x₀ - ι a₀ = ι (f.eval a₀) * (-(↑u⁻¹ : AdjoinRoot f ⧸ J)) := by
    have : (x₀ - ι a₀) * ↑u = -ι (f.eval a₀) := by
      rw [hu]; exact eq_neg_of_add_eq_zero_right hfx₀ |> fun h => by rw [add_comm] at hfx₀; exact eq_neg_of_add_eq_zero_left hfx₀
    calc x₀ - ι a₀ = (x₀ - ι a₀) * ↑u * ↑u⁻¹ := by rw [Units.mul_inv_cancel_right]
      _ = ι (f.eval a₀) * (-(↑u⁻¹ : AdjoinRoot f ⧸ J)) := by rw [this]; ring

  haveI : Module.Finite S (AdjoinRoot f ⧸ J) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ S J).toLinearMap (Ideal.Quotient.mkₐ_surjective S J)
  have hsurj : Function.Surjective ι := by
    set N : Submodule S (AdjoinRoot f ⧸ J) := LinearMap.range (Algebra.linearMap S (AdjoinRoot f ⧸ J)) with hN
    have key : (⊤ : Submodule S (AdjoinRoot f ⧸ J)) ≤ N ⊔ (maximalIdeal S) • ⊤ := by
      rintro c -
      obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
      obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective c'

      obtain ⟨h, hh⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (a := a₀) (p := p)
      have hdec : (Ideal.Quotient.mk J) (AdjoinRoot.mk f p) =
          ι (p.eval a₀) + ι (f.eval a₀) * (-(↑u⁻¹ : AdjoinRoot f ⧸ J) * π (AdjoinRoot.mk f h)) := by
        have : AdjoinRoot.mk f p = AdjoinRoot.of f (p.eval a₀) + (AdjoinRoot.root f - AdjoinRoot.of f a₀) * AdjoinRoot.mk f h := by
          have hp : p = C (p.eval a₀) + (X - C a₀) * h := by rw [← hh]; ring
          conv_lhs => rw [hp]
          rw [map_add, map_mul, map_sub, AdjoinRoot.mk_C, AdjoinRoot.mk_X, AdjoinRoot.mk_C]
        rw [show (Ideal.Quotient.mk J) (AdjoinRoot.mk f p) = π (AdjoinRoot.mk f p) from rfl, this,
          map_add, map_mul, map_sub]
        show ι (p.eval a₀) + (x₀ - ι a₀) * π (AdjoinRoot.mk f h) = _
        rw [hx₀a₀]; ring
      rw [hdec]
      refine Submodule.add_mem_sup ⟨p.eval a₀, rfl⟩ ?_
      rw [hιalg, Algebra.algebraMap_eq_smul_one, smul_mul_assoc]
      exact Submodule.smul_mem_smul h₁ Submodule.mem_top
    have hle := Submodule.le_of_le_smul_of_le_jacobson_bot (N := N) (N' := ⊤) Module.Finite.fg_top
      (IsLocalRing.maximalIdeal_le_jacobson _) key
    intro c
    obtain ⟨s, hs⟩ := hle (Submodule.mem_top : c ∈ ⊤)
    exact ⟨s, hs⟩

  have hinj : Function.Injective ι := by
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
    intro s hs
    have hsJ : AdjoinRoot.of f s ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp hs

    have hse : s • e₀ = 0 := by
      rw [hJ, Ideal.mem_span_singleton'] at hsJ
      obtain ⟨c, hc⟩ := hsJ
      rw [Algebra.smul_def, AdjoinRoot.algebraMap_eq, ← hc, mul_assoc, sub_mul, one_mul, he₀idem, sub_self, mul_zero]
    set B := (AdjoinRoot.powerBasis' hf).basis with hB
    have hcoord : ∀ i, s * B.repr e₀ i = 0 := fun i => by
      have := congrArg (fun v => B.repr v i) hse
      simp only [map_smul, map_zero, Finsupp.smul_apply, Finsupp.coe_zero, Pi.zero_apply, smul_eq_mul] at this
      exact this

    have hex : ∃ i, B.repr e₀ i ∉ maximalIdeal S := by
      by_contra hall
      push Not at hall
      apply he₀not
      rw [← B.sum_repr e₀]
      refine Ideal.sum_mem _ fun i _ => ?_
      rw [Algebra.smul_def]
      refine Ideal.mul_mem_right _ _ ?_
      rw [RingHom.mem_ker, AdjoinRoot.algebraMap_eq, hφof, IsLocalRing.residue_eq_zero_iff]
      exact hall i
    obtain ⟨i, hi⟩ := hex
    have hu' : IsUnit (B.repr e₀ i) := by
      by_contra hnu; exact hi ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
    exact (hu'.mul_right_eq_zero.mp (by rw [mul_comm]; exact hcoord i))

  obtain ⟨a, ha⟩ := hsurj x₀
  refine ⟨a, ?_, ?_⟩
  ·
    show f.eval a = 0
    apply hinj
    rw [map_zero, ← Polynomial.eval₂_at_apply, ha, hx₀, hι, ← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root,
      map_zero]
  · obtain ⟨t, ht⟩ := hsurj (-(↑u⁻¹ : AdjoinRoot f ⧸ J))
    have : ι (a - a₀ - f.eval a₀ * t) = 0 := by
      rw [map_sub, map_sub, map_mul, ha, ht, ← hx₀a₀, sub_self]
    have h0 : a - a₀ - f.eval a₀ * t = 0 := hinj (this.trans (map_zero ι).symm)
    rw [sub_eq_zero] at h0
    rw [h0]
    exact Ideal.mul_mem_right _ _ h₁

end HensFinAux

open HensFinAux in

theorem solution
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {S : Type v} [CommRing S] [IsLocalRing S] [Algebra R S] [Module.Finite R S] :
    HenselianLocalRing S := by
  exact { is_henselian := fun f hf a₀ h₁ h₂ => HensFinAux.main R f hf a₀ h₁ h₂ }

end S_HenselianLocalRing_of_moduleFinite_of_isLocalRing
end P2MW
export P2MW.S_HenselianLocalRing_of_moduleFinite_of_isLocalRing (solution)
