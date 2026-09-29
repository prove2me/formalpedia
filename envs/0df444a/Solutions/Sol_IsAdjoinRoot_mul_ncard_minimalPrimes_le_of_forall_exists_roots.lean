-- Prove2me | solution 1 for IsAdjoinRoot.mul_ncard_minimalPrimes_le_of_forall_exists_roots
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/173cc549-c910-5822-b523-bddbaf77a5dc

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsAdjoinRoot_mul_ncard_minimalPrimes_le_of_forall_exists_roots

set_option autoImplicit false

theorem solution
    (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    (f : Polynomial R) (hf : f.Monic) (hS : IsAdjoinRoot S f) (n : ℕ)
    (hroots : ∀ 𝔭 ∈ minimalPrimes R, ∃ s : Finset (FractionRing (R ⧸ 𝔭)), n ≤ s.card ∧
      ∀ z ∈ s, (f.map (algebraMap R (FractionRing (R ⧸ 𝔭)))).IsRoot z)
    (hfin : (minimalPrimes S).Finite) :
    n * (minimalPrimes R).ncard ≤ (minimalPrimes S).ncard := by
  classical

  by_cases hR : (minimalPrimes R).Finite
  swap
  · rw [Set.Infinite.ncard hR, mul_zero]; exact Nat.zero_le _

  haveI : Module.Finite R S := Module.Finite.of_basis (IsAdjoinRootMonic.basis ⟨hS, hf⟩)
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S

  have key : ∀ 𝔭 ∈ minimalPrimes R, ∃ T : Finset (Ideal S), n ≤ T.card ∧ (↑T : Set (Ideal S)) ⊆ minimalPrimes S ∧
      ∀ 𝔓 ∈ T, 𝔓.comap (algebraMap R S) = 𝔭 := by
    intro 𝔭 h𝔭
    haveI h𝔭p : 𝔭.IsPrime := h𝔭.1.1
    obtain ⟨s, hn, hs⟩ := hroots 𝔭 h𝔭

    have hev : ∀ z ∈ s, Polynomial.eval₂ (algebraMap R (FractionRing (R ⧸ 𝔭))) z f = 0 := by
      intro z hz
      rw [Polynomial.eval₂_eq_eval_map]; exact hs z hz
    let φ : ↥s → (S →+* FractionRing (R ⧸ 𝔭)) := fun z => hS.lift (algebraMap R _) z.1 (hev z.1 z.2)
    have hφroot : ∀ z : ↥s, φ z hS.root = z.1 := fun z => hS.lift_root _
    have hφalg : ∀ (z : ↥s) (a : R), φ z (algebraMap R S a) = algebraMap R (FractionRing (R ⧸ 𝔭)) a :=
      fun z a => hS.lift_algebraMap _ a
    have halg : ∀ a : R, algebraMap R (FractionRing (R ⧸ 𝔭)) a = 0 ↔ a ∈ 𝔭 := by
      intro a
      rw [IsScalarTower.algebraMap_apply R (R ⧸ 𝔭) (FractionRing (R ⧸ 𝔭)), ← map_zero (algebraMap (R ⧸ 𝔭) _),
        (IsFractionRing.injective (R ⧸ 𝔭) (FractionRing (R ⧸ 𝔭))).eq_iff, Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem]

    let P : ↥s → Ideal S := fun z => RingHom.ker (φ z)
    have hPprime : ∀ z, (P z).IsPrime := fun z => RingHom.ker_isPrime _
    have hPcomap : ∀ z, (P z).comap (algebraMap R S) = 𝔭 := by
      intro z; ext a
      rw [Ideal.mem_comap, RingHom.mem_ker, hφalg, halg]
    have hPmin : ∀ z, P z ∈ minimalPrimes S := by
      intro z
      refine ⟨⟨hPprime z, bot_le⟩, ?_⟩
      rintro Q ⟨hQ, -⟩ hQle

      by_contra hne
      have hlt : Q < P z := lt_of_le_of_ne hQle (fun h => hne (h ▸ le_rfl))
      obtain ⟨y, hyP, hyQ⟩ := Set.exists_of_ssubset hlt
      haveI := hQ
      have := Ideal.comap_lt_comap_of_integral_mem_sdiff hQle ⟨hyP, hyQ⟩ (Algebra.IsIntegral.isIntegral (R := R) y)
      rw [hPcomap] at this
      have hQc : (Q.comap (algebraMap R S)).IsPrime := Ideal.comap_isPrime _ _
      exact absurd (h𝔭.2 ⟨hQc, bot_le⟩ this.le) (not_le_of_gt this)
    have hPinj : Function.Injective P := by
      intro z z' hzz'
      by_contra hne
      have hne' : z.1 ≠ z'.1 := fun h => hne (Subtype.ext h)

      obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := R ⧸ 𝔭) z.1
      obtain ⟨a₀, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨b₀, rfl⟩ := Ideal.Quotient.mk_surjective b
      have hb0 : algebraMap R (FractionRing (R ⧸ 𝔭)) b₀ ≠ 0 := by
        rw [Ne, halg, ← Ideal.Quotient.eq_zero_iff_mem]; exact nonZeroDivisors.ne_zero hb

      have hw : algebraMap R S b₀ * hS.root - algebraMap R S a₀ ∈ P z := by
        rw [RingHom.mem_ker, map_sub, map_mul, hφroot, hφalg, hφalg, ← hab,
          IsScalarTower.algebraMap_apply R (R ⧸ 𝔭) (FractionRing (R ⧸ 𝔭)),
          IsScalarTower.algebraMap_apply R (R ⧸ 𝔭) (FractionRing (R ⧸ 𝔭)), Ideal.Quotient.algebraMap_eq,
          div_eq_mul_inv, sub_eq_zero]
        rw [mul_comm, mul_assoc, inv_mul_cancel₀, mul_one]
        rw [Ne, ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]; exact hb0
      have hw' : algebraMap R S b₀ * hS.root - algebraMap R S a₀ ∉ P z' := by
        rw [RingHom.mem_ker, map_sub, map_mul, hφroot, hφalg, hφalg, sub_eq_zero]
        intro h
        apply hne'
        have hz : z.1 = algebraMap R (FractionRing (R ⧸ 𝔭)) a₀ / algebraMap R (FractionRing (R ⧸ 𝔭)) b₀ := by
          rw [← hab]; rfl
        rw [hz, div_eq_iff hb0, mul_comm]
        exact h.symm
      rw [hzz'] at hw
      exact hw' hw
    refine ⟨s.attach.image P, ?_, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ hPinj, Finset.card_attach]; exact hn
    · intro 𝔓 h𝔓
      obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp h𝔓
      exact hPmin z
    · intro 𝔓 h𝔓
      obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp h𝔓
      exact hPcomap z

  choose T hTn hTmin hTcomap using key
  let T' : ↥(minimalPrimes R) → Finset (Ideal S) := fun 𝔭 => T 𝔭.1 𝔭.2
  haveI : Fintype ↥(minimalPrimes R) := hR.fintype
  have hdisj : (↑(Finset.univ : Finset ↥(minimalPrimes R)) : Set ↥(minimalPrimes R)).PairwiseDisjoint T' := by
    intro 𝔭 _ 𝔭' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro 𝔓 h1 h2
    apply hne
    exact Subtype.ext ((hTcomap _ _ 𝔓 h1).symm.trans (hTcomap _ _ 𝔓 h2))
  have hsub : (↑(Finset.univ.biUnion T') : Set (Ideal S)) ⊆ minimalPrimes S := by
    intro 𝔓 h𝔓
    obtain ⟨𝔭, -, h⟩ := Finset.mem_biUnion.mp h𝔓
    exact hTmin _ _ h
  calc n * (minimalPrimes R).ncard = ∑ 𝔭 : ↥(minimalPrimes R), n := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm, Set.fintypeCard_eq_ncard]
    _ ≤ ∑ 𝔭 : ↥(minimalPrimes R), (T' 𝔭).card := Finset.sum_le_sum fun 𝔭 _ => hTn _ _
    _ = (Finset.univ.biUnion T').card := (Finset.card_biUnion hdisj).symm
    _ = (↑(Finset.univ.biUnion T') : Set (Ideal S)).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ (minimalPrimes S).ncard := Set.ncard_le_ncard hsub hfin

end S_IsAdjoinRoot_mul_ncard_minimalPrimes_le_of_forall_exists_roots
end P2MW
export P2MW.S_IsAdjoinRoot_mul_ncard_minimalPrimes_le_of_forall_exists_roots (solution)
