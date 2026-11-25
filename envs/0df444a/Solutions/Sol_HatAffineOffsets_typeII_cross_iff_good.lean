-- Prove2me | solution 1 for HatAffineOffsets.typeII_cross_iff_good
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:20:46.379175+00:00
-- url     : https://prove2.me/submissions/39cc75c8-1638-4819-a0bc-4ab35c889032

import Definitions.Def_HatAffineOffsets_TypeI
import Definitions.Def_HatAffineOffsets_TypeII
import Theorems.Thm_HatAffineOffsets_puncturedPairs_card
import Theorems.Thm_HatAffineOffsets_puncturedLine_card
import Theorems.Thm_HatAffineGenericCore_mem_coeffSupport
import Theorems.Thm_HatAffineGenericCore_mem_puncturedValues
import Theorems.Thm_HatAffineGenericCore_puncturedValues_card
attribute [local simp] HatAffineGenericCore.mem_coeffSupport
attribute [local simp] HatAffineGenericCore.mem_puncturedValues
attribute [local simp] HatAffineGenericCore.puncturedValues_card



set_option autoImplicit true
open HatAffineOffsets
universe u
open Finset
attribute [local instance] HatAffineOffsets._p2m_local_instance_68713dd93e_9
namespace HatAffineOffsets
theorem _root_.solution
    {K : Type u} [Field K] [Fintype K]
    (hq : 4 <= Fintype.card K)
    (c d : Fin (Fintype.card K - 1) -> K)
    (hc : forall i, c i ≠ 0)
    (hsurj : forall z : K, z ≠ 0 -> exists i, c i = z) :
    TypeIICross c d ↔ TypeIIGood c d := by
  classical
  constructor
  · rintro ⟨a, beta, hcross⟩
    let e : Fin (Fintype.card K - 1) -> K :=
      fun i => d i - (a - c i * beta)
    let P : Finset (K × K) := puncturedPairs K
    let L : Fin (Fintype.card K - 1) -> Finset (K × K) :=
      fun i => puncturedLine (c i) (e i)
    have hcover : P ⊆ Finset.univ.biUnion L := by
      intro p hp
      have hpP : p ∈ puncturedPairs K := by simpa [P] using hp
      have hpNZ := Finset.mem_product.mp hpP
      have hs0 : p.1 ≠ 0 := by
        simpa [nonzeroFinset] using hpNZ.1
      have ht0 : p.2 ≠ 0 := by
        simpa [nonzeroFinset] using hpNZ.2
      by_contra hnone
      have hnoline : forall i, p.1 - c i * p.2 ≠ e i := by
        intro i hi
        apply hnone
        apply Finset.mem_biUnion.mpr
        refine ⟨i, Finset.mem_univ i, ?_⟩
        exact Finset.mem_filter.mpr ⟨hpP, hi⟩
      let U : K := p.1 + a
      let V : K := p.2 + beta
      have hUa : U ≠ a := by
        intro h
        apply hs0
        calc
          p.1 = U - a := by simp [U]
          _ = 0 := by rw [h]; exact sub_self _
      have hVb : V ≠ beta := by
        intro h
        apply ht0
        calc
          p.2 = V - beta := by simp [V]
          _ = 0 := by rw [h]; exact sub_self _
      have hactive : forall i, U - c i * V ≠ d i := by
        intro i hi
        apply hnoline i
        calc
          p.1 - c i * p.2 =
              (U - c i * V) - (a - c i * beta) := by
            simp only [U, V]
            ring
          _ = d i - (a - c i * beta) := by rw [hi]
          _ = e i := rfl
      rcases hcross U V hactive with hU | hV
      · exact hUa hU
      · exact hVb hV
    have hezero : forall i, e i = 0 := by
      intro i0
      by_contra hi0
      have hline_le : ∀ i ∈ (Finset.univ :
          Finset (Fin (Fintype.card K - 1))),
          (L i).card <= Fintype.card K - 1 := by
        intro i hi
        rw [show L i = puncturedLine (c i) (e i) by rfl,
          puncturedLine_card hq (c i) (e i) (hc i)]
        split <;> omega
      have hline_lt :
          (L i0).card < Fintype.card K - 1 := by
        rw [show L i0 = puncturedLine (c i0) (e i0) by rfl,
          puncturedLine_card hq (c i0) (e i0) (hc i0), if_neg hi0]
        omega
      have hsum_lt :
          (∑ i : Fin (Fintype.card K - 1), (L i).card) <
            ∑ i : Fin (Fintype.card K - 1), (Fintype.card K - 1) := by
        apply Finset.sum_lt_sum hline_le
        exact ⟨i0, Finset.mem_univ i0, hline_lt⟩
      have himpossible : P.card < P.card := by
        calc
          P.card <= (Finset.univ.biUnion L).card :=
            Finset.card_le_card hcover
          _ <= ∑ i : Fin (Fintype.card K - 1), (L i).card :=
            Finset.card_biUnion_le
          _ < ∑ i : Fin (Fintype.card K - 1),
              (Fintype.card K - 1) := hsum_lt
          _ = (Fintype.card K - 1) ^ 2 := by
            simp [pow_two]
          _ = P.card := by rw [show P = puncturedPairs K by rfl,
            puncturedPairs_card]
      exact (Nat.lt_irrefl P.card) himpossible
    refine ⟨a, beta, ?_⟩
    intro i
    have hi := hezero i
    change d i - (a - c i * beta) = 0 at hi
    exact sub_eq_zero.mp hi
  · rintro ⟨a, beta, hd⟩
    refine ⟨a, beta, ?_⟩
    intro U V hactive
    by_cases hU : U = a
    · exact Or.inl hU
    by_cases hV : V = beta
    · exact Or.inr hV
    exfalso
    let z : K := (U - a) / (V - beta)
    have hz : z ≠ 0 :=
      div_ne_zero (sub_ne_zero.mpr hU) (sub_ne_zero.mpr hV)
    obtain ⟨i, hci⟩ := hsurj z hz
    apply hactive i
    rw [hd i, hci]
    dsimp [z]
    field_simp [sub_ne_zero.mpr hV]
    ring
end HatAffineOffsets
