-- Prove2me | solution 1 for NumberField.InfPlaceDecomp.card_tateH0_units_eq_card_and_subsingleton_tateHneg1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/e1bf1b6b-697e-58bf-aff4-3b3438481e60

import Mathlib
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_GroupCohomology_TateCohomology
import Theorems.Thm_NumberField_InfPlaceDecomp_extensionEmbedding_smul_of_ne_one
import Theorems.Thm_Rep_nonempty_tate_addEquiv_elementwise
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_InfPlaceDecomp_card_tateH0_units_eq_card_and_subsingleton_tateHneg1

set_option autoImplicit false
open NumberField
open scoped NumberField.InfPlaceDecomp
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

namespace P2mS26ArchA2

theorem exists_conj_div_eq {s : ℂ} (hs : s * (starRingEnd ℂ) s = 1) :
    ∃ z : ℂ, z ≠ 0 ∧ (starRingEnd ℂ) z / z = s := by
  by_cases h : s = -1
  · refine ⟨Complex.I, Complex.I_ne_zero, ?_⟩
    rw [h, Complex.conj_I, neg_div, div_self Complex.I_ne_zero]
  · have hne : 1 + (starRingEnd ℂ) s ≠ 0 := by
      intro h0
      apply h
      have h1 : (starRingEnd ℂ) (1 + (starRingEnd ℂ) s) = 0 := by rw [h0, map_zero]
      rw [map_add, map_one, Complex.conj_conj] at h1
      exact eq_neg_of_add_eq_zero_right h1
    refine ⟨1 + (starRingEnd ℂ) s, hne, ?_⟩
    rw [div_eq_iff hne, map_add, map_one, Complex.conj_conj, mul_add, mul_one, hs, add_comm]

theorem exists_mul_conj_eq_iff {r : ℂ} (hr : (starRingEnd ℂ) r = r) :
    (∃ z : ℂ, z ≠ 0 ∧ z * (starRingEnd ℂ) z = r) ↔ 0 < r.re := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [Complex.mul_conj, Complex.ofReal_re]
    exact Complex.normSq_pos.2 hz
  · intro h
    refine ⟨(Real.sqrt r.re : ℂ), Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 h).ne', ?_⟩
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt h.le]
    exact Complex.conj_eq_iff_re.1 hr

end P2mS26ArchA2

theorem solution (E K : Type) [Field E] [Field K] [Algebra E K]
    (w : InfinitePlace K) [Fintype (NumberField.InfPlaceDecomp.decomp E K w)] :
    Nat.card (Rep.ofMulDistribMulAction (NumberField.InfPlaceDecomp.decomp E K w) (w.Completion)ˣ).tateH0 =
      Nat.card (NumberField.InfPlaceDecomp.decomp E K w) ∧
    Subsingleton (Rep.ofMulDistribMulAction (NumberField.InfPlaceDecomp.decomp E K w) (w.Completion)ˣ).tateHneg1 := by
  classical
  let G := NumberField.InfPlaceDecomp.decomp E K w
  let L := w.Completion
  by_cases htriv : ∀ σ : G, σ = 1
  ·
    have hg : ∀ x : G, x ∈ Subgroup.zpowers (1 : G) := fun x => by rw [htriv x]; exact Subgroup.one_mem _
    have hD : ∀ x : Lˣ, (1 : Lˣ →* Lˣ) x = (1 : G) • x / x := fun x => by
      rw [MonoidHom.one_apply, one_smul, div_self']
    have hcard1 : Fintype.card G = 1 := Fintype.card_eq_one_iff.2 ⟨1, htriv⟩
    have hN : ∀ x : Lˣ, MonoidHom.id Lˣ x = ∏ h : G, h • x := fun x => by
      rw [Finset.prod_congr rfl (fun h _ => by rw [htriv h, one_smul] : ∀ h ∈ (Finset.univ : Finset G), h • x = x),
        Finset.prod_const, Finset.card_univ, hcard1, pow_one, MonoidHom.id_apply]
    obtain ⟨⟨e0⟩, ⟨e1⟩⟩ := Rep.nonempty_tate_addEquiv_elementwise (1 : G) hg (1 : Lˣ →* Lˣ) (MonoidHom.id Lˣ) hD hN
    have htop : (MonoidHom.id Lˣ).range.subgroupOf (1 : Lˣ →* Lˣ).ker = ⊤ :=
      Subgroup.subgroupOf_eq_top.2 fun x _ => ⟨(x : Lˣ), rfl⟩
    haveI : Subsingleton ((1 : Lˣ →* Lˣ).ker ⧸ (MonoidHom.id Lˣ).range.subgroupOf (1 : Lˣ →* Lˣ).ker) := by
      rw [htop]; exact QuotientGroup.subsingleton_quotient_top
    have htop' : (1 : Lˣ →* Lˣ).range.subgroupOf (MonoidHom.id Lˣ).ker = ⊤ :=
      Subgroup.subgroupOf_eq_top.2 fun x hx => by
        rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hx
        rw [hx]; exact one_mem _
    haveI : Subsingleton ((MonoidHom.id Lˣ).ker ⧸ (1 : Lˣ →* Lˣ).range.subgroupOf (MonoidHom.id Lˣ).ker) := by
      rw [htop']; exact QuotientGroup.subsingleton_quotient_top
    haveI : Subsingleton G := ⟨fun a b => by rw [htriv a, htriv b]⟩
    refine ⟨?_, e1.toEquiv.subsingleton⟩
    calc Nat.card _ = Nat.card (Additive ((1 : Lˣ →* Lˣ).ker ⧸ (MonoidHom.id Lˣ).range.subgroupOf (1 : Lˣ →* Lˣ).ker)) :=
          Nat.card_congr e0.toEquiv
      _ = 1 := Nat.card_of_subsingleton 0
      _ = Nat.card G := (Nat.card_of_subsingleton (1 : G)).symm
  ·
    obtain ⟨σ, hσ⟩ := not_forall.1 htriv
    have hσ' : (σ : K ≃ₐ[E] K) ≠ 1 := fun h => hσ (Subtype.ext h)
    have hconj : ComplexEmbedding.IsConj w.embedding (σ : K ≃ₐ[E] K) := by
      have h2 : (σ : K ≃ₐ[E] K) ∈ MulAction.stabilizer (K ≃ₐ[E] K) (InfinitePlace.mk w.embedding) := by
        rw [InfinitePlace.mk_embedding]; exact σ.2
      rcases (InfinitePlace.mem_stabilizer_mk_iff _ _).1 h2 with h | h
      · exact absurd h hσ'
      · exact h
    have hG : ∀ τ : G, τ = 1 ∨ τ = σ := fun τ => by
      have h2 : (τ : K ≃ₐ[E] K) ∈ MulAction.stabilizer (K ≃ₐ[E] K) (InfinitePlace.mk w.embedding) := by
        rw [InfinitePlace.mk_embedding]; exact τ.2
      rcases (InfinitePlace.mem_stabilizer_mk_iff _ _).1 h2 with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext (h.ext hconj))
    have hg : ∀ x : G, x ∈ Subgroup.zpowers σ := fun x => by
      rcases hG x with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.mem_zpowers σ
    have h1σ : (1 : G) ≠ σ := fun h => hσ h.symm
    have huniv : (Finset.univ : Finset G) = {1, σ} := by
      ext τ
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      exact hG τ
    have hcardG : Nat.card G = 2 := by
      rw [Nat.card_eq_fintype_card, ← Finset.card_univ, huniv, Finset.card_pair h1σ]

    have hw : w.IsComplex := by
      rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff]
      intro hreal
      exact hσ' (hconj.ext (ComplexEmbedding.isConj_one_iff.2 hreal))
    set ι := InfinitePlace.Completion.extensionEmbedding w with hι
    have hbij : Function.Bijective ι := InfinitePlace.Completion.bijective_extensionEmbedding_of_isComplex hw
    have hιinj : Function.Injective ι := hbij.1
    have hA1 : ∀ x : L, ι (σ • x) = starRingEnd ℂ (ι x) := fun x =>
      NumberField.InfPlaceDecomp.extensionEmbedding_smul_of_ne_one E K w σ hσ x

    let D : Lˣ →* Lˣ := MulDistribMulAction.toMonoidHom Lˣ σ / MonoidHom.id Lˣ
    let N : Lˣ →* Lˣ := ∏ h : G, MulDistribMulAction.toMonoidHom Lˣ h
    have hD : ∀ x : Lˣ, D x = σ • x / x := fun x => rfl
    have hN : ∀ x : Lˣ, N x = ∏ h : G, h • x := fun x => by
      show (∏ h : G, MulDistribMulAction.toMonoidHom Lˣ h) x = _
      rw [MonoidHom.finsetProd_apply]; rfl
    have hN2 : ∀ x : Lˣ, N x = x * σ • x := fun x => by
      rw [hN, huniv, Finset.prod_pair h1σ, one_smul]
    obtain ⟨⟨e0⟩, ⟨e1⟩⟩ := Rep.nonempty_tate_addEquiv_elementwise σ hg D N hD hN

    have hker : ∀ u : Lˣ, u ∈ D.ker ↔ starRingEnd ℂ (ι u) = ι u := fun u => by
      rw [MonoidHom.mem_ker, hD, div_eq_one, Units.ext_iff, NumberField.InfPlaceDecomp.coe_smul_units, ← hA1, hιinj.eq_iff]
    have hrange : ∀ u : Lˣ, u ∈ N.range ↔ ∃ z : ℂ, z ≠ 0 ∧ z * starRingEnd ℂ z = ι u := fun u => by
      constructor
      · rintro ⟨v, rfl⟩
        refine ⟨ι v, (map_ne_zero ι).2 v.ne_zero, ?_⟩
        rw [hN2, Units.val_mul, map_mul, NumberField.InfPlaceDecomp.coe_smul_units, hA1]
      · rintro ⟨z, hz, hzu⟩
        obtain ⟨y, rfl⟩ := hbij.2 z
        have hy : y ≠ 0 := fun h => hz (by rw [h, map_zero])
        refine ⟨Units.mk0 y hy, Units.ext (hιinj ?_)⟩
        rw [hN2, Units.val_mul, map_mul, NumberField.InfPlaceDecomp.coe_smul_units, Units.val_mk0, hA1, hzu]
    refine ⟨?_, ?_⟩
    ·
      rw [Nat.card_congr e0.toEquiv, hcardG]
      show (N.range.subgroupOf D.ker).index = 2
      rw [Subgroup.index_eq_two_iff]
      have hneg1 : (-1 : Lˣ) ∈ D.ker := by
        rw [hker, Units.val_neg, Units.val_one, map_neg, map_one, map_neg, map_one]
      refine ⟨⟨-1, hneg1⟩, fun b => ?_⟩
      have hb : starRingEnd ℂ (ι (b : Lˣ)) = ι (b : Lˣ) := (hker b).1 b.2
      have hre : (ι (b : Lˣ)).re ≠ 0 := by
        intro h0
        apply (map_ne_zero ι).2 (b : Lˣ).ne_zero
        apply Complex.ext
        · rw [h0, Complex.zero_re]
        · rw [Complex.conj_eq_iff_im.1 hb, Complex.zero_im]
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul, hrange, hrange]
      have hval : ι (((b : Lˣ) * ((⟨-1, hneg1⟩ : D.ker) : Lˣ) : Lˣ) : L) = -ι (b : Lˣ) := by
        show ι (((b : Lˣ) * (-1 : Lˣ) : Lˣ) : L) = -ι (b : Lˣ)
        rw [Units.val_mul, Units.val_neg, Units.val_one, map_mul, map_neg, map_one, mul_neg, mul_one]
      rw [hval, P2mS26ArchA2.exists_mul_conj_eq_iff (by rw [map_neg, hb]), P2mS26ArchA2.exists_mul_conj_eq_iff hb,
        Complex.neg_re]
      rcases lt_or_gt_of_ne hre with h | h
      · exact Or.inl ⟨neg_pos.2 h, not_lt.2 h.le⟩
      · exact Or.inr ⟨h, not_lt.2 (neg_nonpos.2 h.le)⟩
    ·
      have hle : N.ker ≤ D.range := by
        intro u hu
        rw [MonoidHom.mem_ker, Units.ext_iff, hN2, Units.val_mul, NumberField.InfPlaceDecomp.coe_smul_units,
          Units.val_one] at hu
        have hs : ι u * starRingEnd ℂ (ι u) = 1 := by rw [← hA1, ← map_mul, hu, map_one]
        obtain ⟨z, hz, hzs⟩ := P2mS26ArchA2.exists_conj_div_eq hs
        obtain ⟨y, rfl⟩ := hbij.2 z
        have hy : y ≠ 0 := fun h => hz (by rw [h, map_zero])
        refine ⟨Units.mk0 y hy, Units.ext (hιinj ?_)⟩
        rw [hD, Units.val_div_eq_div_val, NumberField.InfPlaceDecomp.coe_smul_units, Units.val_mk0, map_div₀, hA1, hzs]
      haveI : Subsingleton (N.ker ⧸ D.range.subgroupOf N.ker) := by
        rw [Subgroup.subgroupOf_eq_top.2 hle]; exact QuotientGroup.subsingleton_quotient_top
      exact e1.toEquiv.subsingleton

end S_NumberField_InfPlaceDecomp_card_tateH0_units_eq_card_and_subsingleton_tateHneg1
end P2MW
export P2MW.S_NumberField_InfPlaceDecomp_card_tateH0_units_eq_card_and_subsingleton_tateHneg1 (solution)
