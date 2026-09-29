-- Prove2me | solution 1 for InverseGalois.inverse_galois_problem_abelian
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T17:53:56.501797+00:00
-- url     : https://prove2.me/submissions/0da48fe4-3d1c-42c1-a88e-6fe2eab05413

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

private theorem realizable_units_zmod (m : ℕ) [NeZero m] :
    IsRealizable ℚ ((ZMod m)ˣ) := by
  have hpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have : NeZero ((m : ℚ)) := ⟨by exact_mod_cast NeZero.ne m⟩
  have hcyc : IsCyclotomicExtension {m} ℚ (CyclotomicField m ℚ) :=
    CyclotomicField.isCyclotomicExtension m ℚ
  exact ⟨⟨{
    L := CyclotomicField m ℚ
    to_field := inferInstance
    to_algebra := inferInstance
    to_isGalois := IsCyclotomicExtension.isGalois {m} ℚ (CyclotomicField m ℚ)
    iso := (IsCyclotomicExtension.autEquivPow (n := m) (CyclotomicField m ℚ)
      (cyclotomic.irreducible_rat hpos)).symm
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

private theorem exists_surj_units (p n : ℕ) (hp : p.Prime) (hn : 1 < n)
    (hd : n ∣ p - 1) :
    ∃ f : (ZMod p)ˣ →* Multiplicative (ZMod n), Function.Surjective f := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero n := ⟨by omega⟩
  have hcard : Nat.card ((ZMod p)ˣ) = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units p]
  have hcard2 : Nat.card (Multiplicative (ZMod n)) = n := by
    rw [Nat.card_eq_fintype_card]
    simp [ZMod.card n]
  exact exists_surjective_of_cyclic inferInstance inferInstance
    (by rw [hcard, hcard2]; exact hd)

private def primeSeq (g : ℕ → ℕ) : ℕ → ℕ
  | 0 => g 0
  | j + 1 => g (primeSeq g j)

private theorem exists_primes (q : ℕ) (hq : q ≠ 0) :
    ∃ f : ℕ → ℕ, (∀ j, (f j).Prime) ∧ (∀ j, f j ≡ 1 [MOD q]) ∧ StrictMono f := by
  have key : ∀ b : ℕ, ∃ p, b < p ∧ p.Prime ∧ p ≡ 1 [MOD q] := fun b =>
    Nat.forall_exists_prime_gt_and_modEq b hq (Nat.coprime_one_left q)
  choose g hg1 hg2 hg3 using key
  refine ⟨primeSeq g, ?_, ?_, ?_⟩
  · intro j
    cases j with
    | zero => exact hg2 0
    | succ j => exact hg2 _
  · intro j
    cases j with
    | zero => exact hg3 0
    | succ j => exact hg3 _
  · refine strictMono_nat_of_lt_succ fun j => ?_
    show primeSeq g j < g (primeSeq g j)
    exact hg1 _

theorem solution {G : Type*} [Fintype G] [CommGroup G] :
    IsRealizable ℚ G := by
  obtain ⟨ι, fι, n, hn1, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite G
  have hq : (∏ i, n i) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    have := hn1 i
    omega
  obtain ⟨f, hfp, hfm, hfs⟩ := exists_primes (∏ i, n i) hq
  let p : ι → ℕ := fun i => f (Fintype.equivFin ι i)
  have hpp : ∀ i, (p i).Prime := fun i => hfp _
  have hpinj : Function.Injective p := by
    intro i j hij
    exact (Fintype.equivFin ι).injective (Fin.val_injective (hfs.injective hij))
  have hcop : Pairwise (Function.onFun Nat.Coprime p) := fun i j hij =>
    (Nat.coprime_primes (hpp i) (hpp j)).2 fun h => hij (hpinj h)
  have hdvd : ∀ i, n i ∣ p i - 1 := by
    intro i
    have h1 : (∏ j, n j) ∣ p i - 1 :=
      (Nat.modEq_iff_dvd' (hpp i).one_lt.le).1 (hfm _).symm
    exact dvd_trans (Finset.dvd_prod_of_mem n (Finset.mem_univ i)) h1
  have hm : (∏ i, p i) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => (hpp i).ne_zero
  have : NeZero (∏ i, p i) := ⟨hm⟩
  have hreal := realizable_units_zmod (∏ i, p i)
  let E : (ZMod (∏ i, p i))ˣ ≃* (∀ i, (ZMod (p i))ˣ) :=
    (Units.mapEquiv (ZMod.prodEquivPi p hcop).toMulEquiv).trans MulEquiv.piUnits
  choose φ hφ using fun i => exists_surj_units (p i) (n i) (hpp i) (hn1 i) (hdvd i)
  let Φ : (∀ i, (ZMod (p i))ˣ) →* (∀ i, Multiplicative (ZMod (n i))) := {
    toFun := fun x i => φ i (x i)
    map_one' := funext fun i => map_one (φ i)
    map_mul' := fun a b => funext fun i => map_mul (φ i) (a i) (b i)
  }
  have hΦ : Function.Surjective Φ := by
    intro y
    exact ⟨fun i => (hφ i (y i)).choose,
      funext fun i => (hφ i (y i)).choose_spec⟩
  refine realizable_of_surjective (A := (ZMod (∏ i, p i))ˣ)
    ((e.symm.toMonoidHom.comp Φ).comp E.toMonoidHom) ?_
  exact (e.symm.surjective.comp hΦ).comp E.surjective
