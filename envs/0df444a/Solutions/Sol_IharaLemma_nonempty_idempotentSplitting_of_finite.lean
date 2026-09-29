-- Prove2me | solution 1 for IharaLemma.nonempty_idempotentSplitting_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/2214835d-3087-5639-a630-30c7965285b3

import Definitions.Def_IharaLemma_IdempotentSplitting
import Theorems.Thm_IharaLemma_isPrecomplete_of_finite
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Tactic.LinearCombination
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IharaLemma_nonempty_idempotentSplitting_of_finite

set_option autoImplicit false

namespace IharaLemmaSolSplit

open IsLocalRing IharaLemma

section Artinian

variable (B : Type) [CommRing B] [IsArtinianRing B]

theorem splitting_of_isArtinianRing : Nonempty (IdempotentSplitting B) := by
  classical
  letI : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  obtain ⟨k, hk⟩ := IsArtinianRing.isNilpotent_nilradical (R := B)

  have hk1 : nilradical B ^ (k + 1) = ⊥ := by
    rw [pow_succ, hk, zero_mul]; rfl

  let Ψ : B ⧸ nilradical B ^ (k + 1) ≃+* ∀ I : MaximalSpectrum B, B ⧸ I.asIdeal ^ (k + 1) :=
    (IsArtinianRing.quotNilradicalPowEquivPi B (k + 1)).toRingEquiv
  let q : B →+* B ⧸ nilradical B ^ (k + 1) := Ideal.Quotient.mk _
  have hq : Function.Bijective q := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      rw [Ideal.Quotient.eq_zero_iff_mem, hk1] at hx
      exact hx
    · exact Ideal.Quotient.mk_surjective
  let Φ : B ≃+* ∀ I : MaximalSpectrum B, B ⧸ I.asIdeal ^ (k + 1) := (RingEquiv.ofBijective q hq).trans Ψ
  have hΦ : ∀ (x : B) (I : MaximalSpectrum B), Φ x I = Ideal.Quotient.mk (I.asIdeal ^ (k + 1)) x := by
    intro x I
    rfl

  let E : MaximalSpectrum B → B := fun I => Φ.symm (Pi.single I 1)
  have hE : CompleteOrthogonalIdempotents E :=
    (CompleteOrthogonalIdempotents.single (fun I : MaximalSpectrum B => B ⧸ I.asIdeal ^ (k + 1))).map
      Φ.symm.toRingHom
  have hEΦ : ∀ I, Φ (E I) = Pi.single I 1 := fun I => Φ.apply_symm_apply _

  have hmem : ∀ I J : MaximalSpectrum B, I ≠ J → E I ∈ J.asIdeal := by
    intro I J hIJ
    have h1 : Φ (E I) J = 0 := by rw [hEΦ, Pi.single_eq_of_ne' hIJ]
    rw [hΦ, Ideal.Quotient.eq_zero_iff_mem] at h1
    exact Ideal.pow_le_self (Nat.succ_ne_zero k) h1
  have hnot : ∀ I : MaximalSpectrum B, E I ∉ I.asIdeal := by
    intro I hI
    apply I.isMaximal.ne_top
    rw [Ideal.eq_top_iff_one, ← hE.complete]
    refine Submodule.sum_mem _ fun J _ => ?_
    by_cases h : J = I
    · rw [h]; exact hI
    · exact hmem J I h

  let n := Fintype.card (MaximalSpectrum B)
  let σ : Fin n ≃ MaximalSpectrum B := (Fintype.equivFin (MaximalSpectrum B)).symm
  refine ⟨{ n := n, e := E ∘ σ, 𝔪 := fun i => (σ i).asIdeal,
            coi := CompleteOrthogonalIdempotents.equiv σ |>.mpr hE,
            isMaximal := fun i => (σ i).isMaximal,
            exists_eq := fun I hI => ⟨σ.symm ⟨I, hI⟩, by simp⟩,
            mem_iff := fun i j => ?_ }⟩
  constructor
  · intro h hij
    subst hij
    exact hnot _ h
  · intro hij
    exact hmem _ _ fun h => hij (σ.injective h)

end Artinian

section Complete

variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
variable {B : Type} [CommRing B] [Algebra 𝒪 B] [Module.Finite 𝒪 B]

abbrev mB (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪] (B : Type) [CommRing B] [Algebra 𝒪 B] : Ideal B :=
  Ideal.map (algebraMap 𝒪 B) (maximalIdeal 𝒪)

omit [IsNoetherianRing 𝒪] [Module.Finite 𝒪 B] in

theorem smodEq_iff_sub_mem_pow (n : ℕ) (x y : B) :
    x ≡ y [SMOD ((maximalIdeal 𝒪) ^ n • ⊤ : Submodule 𝒪 B)] ↔ x - y ∈ mB 𝒪 B ^ n := by
  rw [SModEq.sub_mem, Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_pow]

theorem eq_of_isIdempotentElem_of_sub_mem {e e' : B} (he : IsIdempotentElem e) (he' : IsIdempotentElem e')
    (h : e - e' ∈ mB 𝒪 B) : e = e' := by
  have h1 : e * e = e := he.eq
  have h2 : e' * e' = e' := he'.eq
  have hx3 : (e - e') ^ 3 = e - e' := by
    linear_combination (e + 1 - 3 * e') * h1 + (3 * e - e' - 1) * h2
  have hmem : ∀ k : ℕ, e - e' ∈ mB 𝒪 B ^ (k + 1) := by
    intro k
    induction k with
    | zero => simpa using h
    | succ k ih =>
      have h3 : (e - e') ^ 3 ∈ mB 𝒪 B ^ ((k + 1) * 3) := by
        rw [pow_mul]
        exact Ideal.pow_mem_pow ih 3
      rw [hx3] at h3
      exact Ideal.pow_le_pow_right (by omega) h3
  have h0 : e - e' = 0 :=
    IsHausdorff.haus (inferInstance : IsHausdorff (maximalIdeal 𝒪) B) (e - e') fun n => by
      rw [smodEq_iff_sub_mem_pow, sub_zero]
      exact Ideal.pow_le_pow_right (Nat.le_succ n) (hmem n)
  exact sub_eq_zero.mp h0

def newton (b : B) : ℕ → B
  | 0 => b
  | n + 1 => 3 * newton b n ^ 2 - 2 * newton b n ^ 3

omit [IsNoetherianRing 𝒪] [Module.Finite 𝒪 B] in
theorem newton_spec {b : B} (hb : b ^ 2 - b ∈ mB 𝒪 B) (n : ℕ) :
    newton b n ^ 2 - newton b n ∈ mB 𝒪 B ^ (n + 1) ∧ newton b n - b ∈ mB 𝒪 B := by
  induction n with
  | zero => exact ⟨by simpa [newton] using hb, by simp [newton]⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    constructor
    · have key : (3 * newton b n ^ 2 - 2 * newton b n ^ 3) ^ 2 - (3 * newton b n ^ 2 - 2 * newton b n ^ 3) =
          (newton b n ^ 2 - newton b n) ^ 2 * (4 * newton b n ^ 2 - 4 * newton b n - 3) := by ring
      rw [newton, key]
      have h3 : (newton b n ^ 2 - newton b n) ^ 2 ∈ mB 𝒪 B ^ ((n + 1) * 2) := by
        rw [pow_mul]
        exact Ideal.pow_mem_pow h1 2
      exact Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right (by omega) h3)
    · have key : 3 * newton b n ^ 2 - 2 * newton b n ^ 3 - b =
          (newton b n - b) + (newton b n ^ 2 - newton b n) * (1 - 2 * newton b n) := by ring
      rw [newton, key]
      exact Ideal.add_mem _ h2 (Ideal.mul_mem_right _ _ (Ideal.pow_le_self (Nat.succ_ne_zero n) h1))

omit [IsNoetherianRing 𝒪] [Module.Finite 𝒪 B] in
theorem newton_succ_sub {b : B} (hb : b ^ 2 - b ∈ mB 𝒪 B) (n : ℕ) :
    newton b (n + 1) - newton b n ∈ mB 𝒪 B ^ (n + 1) := by
  have key : 3 * newton b n ^ 2 - 2 * newton b n ^ 3 - newton b n =
      (newton b n ^ 2 - newton b n) * (1 - 2 * newton b n) := by ring
  rw [newton, key]
  exact Ideal.mul_mem_right _ _ (newton_spec hb n).1

omit [IsNoetherianRing 𝒪] [Module.Finite 𝒪 B] in
theorem newton_sub_of_le {b : B} (hb : b ^ 2 - b ∈ mB 𝒪 B) {m n : ℕ} (hmn : m ≤ n) :
    newton b n - newton b m ∈ mB 𝒪 B ^ (m + 1) := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    have key : newton b (n + 1) - newton b m = (newton b (n + 1) - newton b n) + (newton b n - newton b m) := by ring
    rw [key]
    exact Ideal.add_mem _ (Ideal.pow_le_pow_right (by omega) (newton_succ_sub hb n)) ih

theorem exists_isIdempotentElem_lift [IsAdicComplete (maximalIdeal 𝒪) 𝒪] {b : B} (hb : b ^ 2 - b ∈ mB 𝒪 B) :
    ∃ e : B, IsIdempotentElem e ∧ e - b ∈ mB 𝒪 B := by
  haveI : IsPrecomplete (maximalIdeal 𝒪) B := IharaLemma.isPrecomplete_of_finite _ _
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete (maximalIdeal 𝒪) B) (f := newton b)
    (fun {m n} hmn => by
      rw [smodEq_iff_sub_mem_pow, ← neg_sub, Ideal.neg_mem_iff]
      exact Ideal.pow_le_pow_right (Nat.le_succ m) (newton_sub_of_le hb hmn))
  have hL' : ∀ n, newton b n - L ∈ mB 𝒪 B ^ n := fun n => (smodEq_iff_sub_mem_pow n _ _).mp (hL n)
  refine ⟨L, ?_, ?_⟩
  · have hmem : ∀ n, L * L - L ∈ mB 𝒪 B ^ n := fun n => by
      have key : L * L - L = (newton b n ^ 2 - newton b n) - (newton b n - L) * (newton b n + L - 1) := by ring
      rw [key]
      exact Ideal.sub_mem _ (Ideal.pow_le_pow_right (Nat.le_succ n) (newton_spec hb n).1)
        (Ideal.mul_mem_right _ _ (hL' n))
    have h0 := IsHausdorff.haus (inferInstance : IsHausdorff (maximalIdeal 𝒪) B) (L * L - L) fun n => by
      rw [smodEq_iff_sub_mem_pow, sub_zero]
      exact hmem n
    exact sub_eq_zero.mp h0
  · have key : L - b = (newton b 1 - b) - (newton b 1 - L) := by ring
    rw [key]
    have h1 := hL' 1
    rw [pow_one] at h1
    exact Ideal.sub_mem _ (newton_spec hb 1).2 h1

omit [IsNoetherianRing 𝒪] in

theorem mB_le_of_isMaximal (M : Ideal B) [hM : M.IsMaximal] : mB 𝒪 B ≤ M := by
  have h1 : (M.comap (algebraMap 𝒪 B)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
  have h2 : maximalIdeal 𝒪 ≤ M.comap (algebraMap 𝒪 B) := (IsLocalRing.eq_maximalIdeal h1).ge
  exact Ideal.map_le_iff_le_comap.mpr h2

variable (𝒪 B) in

theorem splitting_of_finite [IsAdicComplete (maximalIdeal 𝒪) 𝒪] :
    Nonempty (IdempotentSplitting B) := by
  classical

  letI : Algebra (ResidueField 𝒪) (B ⧸ mB 𝒪 B) := inferInstanceAs (Algebra (𝒪 ⧸ _) _)
  haveI : IsScalarTower 𝒪 (ResidueField 𝒪) (B ⧸ mB 𝒪 B) := inferInstanceAs (IsScalarTower 𝒪 (𝒪 ⧸ _) _)
  haveI : Module.Finite (ResidueField 𝒪) (B ⧸ mB 𝒪 B) := Module.Finite.of_restrictScalars_finite 𝒪 _ _
  haveI : IsArtinianRing (B ⧸ mB 𝒪 B) := isArtinian_of_tower (ResidueField 𝒪) inferInstance
  obtain ⟨S⟩ := splitting_of_isArtinianRing (B ⧸ mB 𝒪 B)

  have hlift : ∀ i : Fin S.n, ∃ E : B, IsIdempotentElem E ∧ Ideal.Quotient.mk (mB 𝒪 B) E = S.e i := by
    intro i
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (S.e i)
    have hb2 : b ^ 2 - b ∈ mB 𝒪 B := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, hb, sq, (S.coi.idem i).eq, sub_self]
    obtain ⟨E, hE, hEb⟩ := exists_isIdempotentElem_lift hb2
    refine ⟨E, hE, ?_⟩
    rw [← hb, Ideal.Quotient.eq]
    exact hEb
  choose E hE hEmk using hlift

  have horth : Pairwise (fun i j => E i * E j = 0) := by
    intro i j hij
    refine eq_of_isIdempotentElem_of_sub_mem (𝒪 := 𝒪) (IsIdempotentElem.mul (hE i) (hE j))
      IsIdempotentElem.zero ?_
    rw [sub_zero, ← Ideal.Quotient.eq_zero_iff_mem, map_mul, hEmk, hEmk]
    exact S.coi.ortho hij
  have hOI : OrthogonalIdempotents E := ⟨hE, horth⟩
  have hsum : ∑ i, E i = 1 := by
    refine eq_of_isIdempotentElem_of_sub_mem (𝒪 := 𝒪) hOI.isIdempotentElem_sum IsIdempotentElem.one ?_
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sum, map_one]
    have hs : ∑ i, Ideal.Quotient.mk (mB 𝒪 B) (E i) = ∑ i, S.e i := Finset.sum_congr rfl fun i _ => hEmk i
    rw [hs, S.coi.complete, sub_self]
  have hCOI : CompleteOrthogonalIdempotents E := ⟨hOI, hsum⟩

  let 𝔐 : Fin S.n → Ideal B := fun i => (S.𝔪 i).comap (Ideal.Quotient.mk (mB 𝒪 B))
  have hmax : ∀ i, (𝔐 i).IsMaximal := fun i => by
    haveI := S.isMaximal i
    exact Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk (mB 𝒪 B)) Ideal.Quotient.mk_surjective
  have hcomap : ∀ (M : Ideal B), M.IsMaximal →
      (M.map (Ideal.Quotient.mk (mB 𝒪 B))).comap (Ideal.Quotient.mk (mB 𝒪 B)) = M := by
    intro M hM
    haveI := hM
    rw [Ideal.comap_map_of_surjective (Ideal.Quotient.mk (mB 𝒪 B)) Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr (mB_le_of_isMaximal M)
  refine ⟨{ n := S.n, e := E, 𝔪 := 𝔐, coi := hCOI, isMaximal := hmax, exists_eq := ?_, mem_iff := ?_ }⟩
  · intro M hM
    haveI := hM
    have hMbar : (M.map (Ideal.Quotient.mk (mB 𝒪 B))).IsMaximal := by
      rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk (mB 𝒪 B))
        Ideal.Quotient.mk_surjective hM with h | h
      · exfalso
        apply hM.ne_top
        rw [← hcomap M hM, h, Ideal.comap_top]
      · exact h
    obtain ⟨i, hi⟩ := S.exists_eq _ hMbar
    refine ⟨i, ?_⟩
    show (S.𝔪 i).comap _ = M
    rw [hi, hcomap M hM]
  · intro i j
    show E i ∈ (S.𝔪 j).comap _ ↔ i ≠ j
    rw [Ideal.mem_comap, hEmk]
    exact S.mem_iff i j

end Complete

end IharaLemmaSolSplit

theorem solution (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    [IsNoetherianRing 𝒪] (B : Type) [CommRing B] [Algebra 𝒪 B] [Module.Finite 𝒪 B]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] :
    Nonempty (IharaLemma.IdempotentSplitting B) :=
  IharaLemmaSolSplit.splitting_of_finite 𝒪 B

end S_IharaLemma_nonempty_idempotentSplitting_of_finite
end P2MW
export P2MW.S_IharaLemma_nonempty_idempotentSplitting_of_finite (solution)
