-- Prove2me | solution 1 for InverseGalois.inverse_galois_problem_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T17:52:36.498168+00:00
-- url     : https://prove2.me/submissions/3f769694-b450-411a-9cd9-6e9e61441621

import Mathlib
import Definitions.Def_InverseGalois_realizability

open InverseGalois IntermediateField Polynomial

universe u v w

private theorem realizable_of_surjective {K : Type u} [Field K] {A : Type v} {B : Type w}
    [Group A] [Group B] [Finite A] [hA : IsRealizable K A] (f : A →* B)
    (hf : Function.Surjective f) : IsRealizable K B := by
  obtain ⟨L, fL, aL, gL, e⟩ := hA.exists_realization.some
  let _ := fL
  let _ := aL
  let _ := gL
  have : Finite (L ≃ₐ[K] L) := Finite.of_equiv A e.toEquiv
  have : FiniteDimensional K L := IsGalois.finiteDimensional_of_finite K L
  let ψ : (L ≃ₐ[K] L) →* B := f.comp e.symm.toMonoidHom
  have hψ : Function.Surjective ψ := hf.comp e.symm.surjective
  exact ⟨⟨{
    L := fixedField ψ.ker
    to_field := inferInstance
    to_algebra := inferInstance
    to_isGalois := inferInstance
    iso := (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.trans
      (IsGalois.normalAutEquivQuotient ψ.ker)
  }⟩⟩

private theorem realizable_units_zmod (p : ℕ) [hp : Fact p.Prime] :
    IsRealizable ℚ ((ZMod p)ˣ) := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have : NeZero ((p : ℚ)) := ⟨by exact_mod_cast hp.out.ne_zero⟩
  have hcyc : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  exact ⟨⟨{
    L := CyclotomicField p ℚ
    to_field := inferInstance
    to_algebra := inferInstance
    to_isGalois := IsCyclotomicExtension.isGalois {p} ℚ (CyclotomicField p ℚ)
    iso := (IsCyclotomicExtension.autEquivPow (n := p) (CyclotomicField p ℚ)
      (cyclotomic.irreducible_rat hp.out.pos)).symm
  }⟩⟩

private theorem exists_surjective_of_cyclic {A : Type v} {B : Type w} [Group A] [Group B]
    (hA : IsCyclic A) (hB : IsCyclic B) (h : Nat.card B ∣ Nat.card A) :
    ∃ f : A →* B, Function.Surjective f := by
  have hf : Function.Surjective (ZMod.castHom h (ZMod (Nat.card B))) :=
    ZMod.castHom_surjective h
  let g : Multiplicative (ZMod (Nat.card A)) →* Multiplicative (ZMod (Nat.card B)) :=
    AddMonoidHom.toMultiplicative (ZMod.castHom h (ZMod (Nat.card B))).toAddMonoidHom
  have hcoe : ∀ x, g x = Multiplicative.ofAdd
      ((ZMod.castHom h (ZMod (Nat.card B))) (Multiplicative.toAdd x)) := fun _ => rfl
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, hx⟩ := hf (Multiplicative.toAdd y)
    exact ⟨Multiplicative.ofAdd x, by rw [hcoe, toAdd_ofAdd, hx, ofAdd_toAdd]⟩
  refine ⟨((zmodCyclicMulEquiv hB).toMonoidHom.comp g).comp
    (zmodCyclicMulEquiv hA).symm.toMonoidHom, ?_⟩
  exact ((zmodCyclicMulEquiv hB).surjective.comp hg).comp
    (zmodCyclicMulEquiv hA).symm.surjective

theorem solution {G : Type*} [Fintype G] [Group G] [IsCyclic G] :
    IsRealizable ℚ G := by
  have hn : Nat.card G ≠ 0 := Nat.card_ne_zero.2 ⟨⟨1⟩, inferInstance⟩
  obtain ⟨p, hp1, hp, hpm⟩ :=
    Nat.forall_exists_prime_gt_and_modEq 1 (q := Nat.card G) (a := 1) hn
      (Nat.coprime_one_left _)
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : Nat.card G ∣ p - 1 := (Nat.modEq_iff_dvd' hp.one_lt.le).1 hpm.symm
  have hcard : Nat.card ((ZMod p)ˣ) = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units p]
  have hreal := realizable_units_zmod p
  obtain ⟨f, hf⟩ := exists_surjective_of_cyclic (A := (ZMod p)ˣ) (B := G)
    inferInstance inferInstance (by rw [hcard]; exact hdvd)
  exact realizable_of_surjective f hf
