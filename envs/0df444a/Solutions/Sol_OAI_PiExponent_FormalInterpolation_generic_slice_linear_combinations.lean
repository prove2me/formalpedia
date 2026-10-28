-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.generic_slice_linear_combinations
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T00:09:25.720526+00:00
-- url     : https://prove2.me/submissions/85bd813c-8499-4941-b2cc-962d0d9c195c

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Definitions.Def_OAI_PiExponent_ComponentLocalLength
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.RingTheory.Length

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem S154_key {K R : Type*} [Field K] [Infinite K] [CommRing R] [IsNoetherianRing R]
    [Algebra K R] {k : ℕ} (f : Fin k → R) (P : Ideal R) [P.IsPrime]
    (hmin : (Ideal.span (Set.range f)).IsMinimalPrime P) (n : ℕ) (hn : (n : ENat) = P.height) :
    ∀ i ≤ n, ∃ g : Fin i → R, (∀ l, g l ∈ Submodule.span K (Set.range f)) ∧
      ∀ Q : Ideal R, Q.IsPrime → Ideal.span (Set.range g) ≤ Q → Q ≤ P → (i : ENat) ≤ Q.height := by
  intro i
  induction i with
  | zero => intro _; exact ⟨Fin.elim0, fun l => l.elim0, fun _ _ _ _ => by simp⟩
  | succ i ih =>
    intro hi
    obtain ⟨g, hgV, hg⟩ := ih (by omega)
    set J := Ideal.span (Set.range g)
    set V := Submodule.span K (Set.range f)
    let T : Set (Ideal R) := {Q | Q ∈ J.minimalPrimes ∧ Q ≤ P ∧ Q.height = i}
    have hT : T.Finite := J.finite_minimalPrimes_of_isNoetherianRing.subset (fun _ h => h.1)
    have : Finite T := hT.to_subtype
    let p : T → Submodule K V := fun Q => ((Q.1).restrictScalars K).comap V.subtype
    have hp : ∀ Q, p Q ≠ ⊤ := by
      rintro ⟨Q, hQJ, hQP, hQh⟩ htop
      have hQprime : Q.IsPrime := hQJ.isPrime
      have hfQ : Ideal.span (Set.range f) ≤ Q := by
        rw [Ideal.span_le]
        rintro _ ⟨j, rfl⟩
        have : (⟨f j, Submodule.subset_span ⟨j, rfl⟩⟩ : V) ∈ p ⟨Q, hQJ, hQP, hQh⟩ := by
          rw [htop]; trivial
        exact this
      have hPQ : P ≤ Q := hmin.2 ⟨hQprime, hfQ⟩ hQP
      have : Q = P := le_antisymm hQP hPQ
      rw [this, ← hn] at hQh
      norm_cast at hQh
      omega
    obtain ⟨x, hx⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
    refine ⟨Matrix.vecCons (x : R) g, ?_, ?_⟩
    · intro l
      refine Fin.cases ?_ (fun l => ?_) l
      · simpa using x.2
      · simp [hgV l]
    · intro Q' hQ' hle hQ'P
      rw [Matrix.range_cons, Ideal.span_union] at hle
      have hxQ' : (x : R) ∈ Q' := hle (Ideal.mem_sup_left (Ideal.subset_span rfl))
      have hJQ' : J ≤ Q' := le_trans le_sup_right hle
      obtain ⟨Q, hQmin, hQQ'⟩ := Ideal.exists_minimalPrimes_le hJQ'
      have hQprime : Q.IsPrime := hQmin.isPrime
      have hQi : (i : ENat) ≤ Q.height := hg Q hQprime hQmin.le (hQQ'.trans hQ'P)
      push_cast
      by_cases hh : Q.height = i
      · have hxQ : (x : R) ∉ Q := hx ⟨Q, hQmin, hQQ'.trans hQ'P, hh⟩
        have hlt : Q < Q' := lt_of_le_of_ne hQQ' (fun h => hxQ (h ▸ hxQ'))
        have := Ideal.height_strict_mono_of_isPrime_of_isPrime hlt
        rw [hh] at this
        exact Order.add_one_le_of_lt this
      · exact (Order.add_one_le_of_lt (lt_of_le_of_ne hQi (Ne.symm hh))).trans (Ideal.height_mono hQQ')

theorem solution
    {m k : Nat} (w : Fin (m + 1) → Rat)
    (hw : ∀ i, 0 < (w i : Real)) (H : Real) (hH : 0 < H)
    (f : Fin k → MvPolynomial (Fin (m + 1)) Complex)
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (hminimal : (Ideal.span (Set.range f)).IsMinimalPrime P)
    (hdegree : ∀ j, logarithmicDegreeBound w H (f j))
    (A : Finset (Fin (m + 1))) (hcard : A.card = P.height)
    (n : Nat) (hn : (n : ENat) = P.height)
    (L : Nat)
    (hlength : componentLocalLength (Ideal.span (Set.range f)) P = (L : ENat))
    (hpos : 0 < P.height) :
    ∃ (g : Fin n → MvPolynomial (Fin (m + 1)) Complex) (M : Nat),
      (∀ i, ∃ c : Fin k → Complex,
        g i = ∑ j, MvPolynomial.C (c j) * f j) ∧
      (∀ i, logarithmicDegreeBound w H (g i)) ∧
      Ideal.radical
        ((Ideal.span (Set.range g)).map
          (algebraMap (MvPolynomial (Fin (m + 1)) Complex)
            (Localization.AtPrime P))) =
        P.map (algebraMap (MvPolynomial (Fin (m + 1)) Complex)
          (Localization.AtPrime P)) ∧
      componentLocalLength (Ideal.span (Set.range g)) P = (M : ENat) ∧
      L ≤ M := by
  classical
  set S := Localization.AtPrime P
  obtain ⟨g, hgV, hg⟩ := S154_key (K := Complex) f P hminimal n hn n le_rfl
  have hc : ∀ i, ∃ c : Fin k → Complex, g i = ∑ j, MvPolynomial.C (c j) * f j := by
    intro i
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Complex).mp (hgV i)
    exact ⟨c, by rw [← hc]; simp [MvPolynomial.C_mul']⟩
  have hgf : Ideal.span (Set.range g) ≤ Ideal.span (Set.range f) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨c, hci⟩ := hc i
    rw [hci]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
  have hPmin : P ∈ (Ideal.span (Set.range g)).minimalPrimes := by
    refine ⟨⟨inferInstance, hgf.trans hminimal.le⟩, fun Q hQ hQP => ?_⟩
    have := hQ.1
    have h1 := hg Q hQ.1 hQ.2 hQP
    exact (Ideal.eq_of_le_of_height_le (I := Q) (J := P) hQP (hn ▸ h1)).ge
  have hrad := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (A := S) P _ hPmin
  set J := (Ideal.span (Set.range g)).map (algebraMap (MvPolynomial (Fin (m + 1)) Complex) S)
  have hJm : J.radical = IsLocalRing.maximalIdeal S := by
    rw [hrad, Localization.AtPrime.map_eq_maximalIdeal]
  have hmJ : IsLocalRing.maximalIdeal S ∈ J.minimalPrimes :=
    ⟨⟨inferInstance, hJm ▸ Ideal.le_radical⟩, fun Q hQ _ => hJm ▸ (hQ.1.radical_le_iff.mpr hQ.2)⟩
  have : IsArtinianRing (S ⧸ J) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing J hmJ
  have : IsArtinian S (S ⧸ J) := isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := J))
  have hfin : Module.length S (S ⧸ J) ≠ ⊤ := Module.length_ne_top
  refine ⟨g, (Module.length S (S ⧸ J)).toNat, hc, ?_, hrad, (ENat.natCast_toNat hfin).symm, ?_⟩
  · intro i a ha
    obtain ⟨c, hci⟩ := hc i
    rw [hci] at ha
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sum] at ha
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
    rw [MvPolynomial.coeff_C_mul] at hj
    exact hdegree j a (MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hj))
  · have hle : J ≤ (Ideal.span (Set.range f)).map (algebraMap (MvPolynomial (Fin (m + 1)) Complex) S) := Ideal.map_mono hgf
    have := Module.length_le_of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)
    have h2 : (L : ENat) ≤ ((Module.length S (S ⧸ J)).toNat : ENat) := by
      rw [ENat.natCast_toNat hfin, ← hlength]; exact this
    exact_mod_cast h2
