-- Prove2me | solution 1 for M4aLocalCFT.fieldUnitsDecomp_norm_ker_le_derive_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/da4e5571-00c4-5ee9-9f45-75cf59075463

import Definitions.Def_M4aLocalCFT_VocabDefs
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aLocalCFT_fieldUnitsDecomp_norm_ker_le_derive_range

set_option Elab.async false
set_option autoImplicit false

namespace M4aLocalCFT
p2m_export "M4aLocalCFT" "fieldUnitsAct fieldUnitsNorm fieldUnitsDerive"
p2m_open "M4aLocalCFT"
namespace CyclicHilbert90

variable {L : Type*} [Field L]

theorem pow_apply_units_injOn (σ : L ≃+* L) {n : ℕ} (hord : orderOf σ = n) :
    Set.InjOn (fun i => (((σ ^ i : L ≃+* L) : L →+* L).toMonoidHom.comp (Units.coeHom L)))
      (Finset.range n) := by
  intro i hi j hj hij
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  have hall : ∀ y : L, (σ ^ i : L ≃+* L) y = (σ ^ j : L ≃+* L) y := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · rw [map_zero, map_zero]
    · have := DFunLike.congr_fun hij (Units.mk0 y hy)
      simpa using this
  have hpow : (σ ^ i : L ≃+* L) = (σ ^ j : L ≃+* L) := RingEquiv.ext hall
  exact pow_injOn_Iio_orderOf (Set.mem_Iio.mpr (by rw [hord]; exact hi))
    (Set.mem_Iio.mpr (by rw [hord]; exact hj)) hpow

theorem exists_mul_map_eq_of_prod_pow_eq_one (σ : L ≃+* L) {n : ℕ} (hn0 : 0 < n)
    (hord : orderOf σ = n) (x : L) (hx : x ≠ 0)
    (hN : ∏ i ∈ Finset.range n, (σ ^ i : L ≃+* L) x = 1) :
    ∃ b : L, b ≠ 0 ∧ x * σ b = b := by
  classical
  set a : ℕ → L := fun i => ∏ j ∈ Finset.range i, (σ ^ j : L ≃+* L) x with ha
  have ha0 : a 0 = 1 := by simp [ha]
  have haN : a n = 1 := hN
  have hane : ∀ i, a i ≠ 0 := by
    intro i
    refine Finset.prod_ne_zero_iff.mpr fun j _ hzero => hx ?_
    have : (σ ^ j : L ≃+* L) x = (σ ^ j : L ≃+* L) 0 := by rw [map_zero]; exact hzero
    exact (σ ^ j : L ≃+* L).injective this
  have haS : ∀ i, x * σ (a i) = a (i + 1) := by
    intro i
    rw [ha]
    simp only [map_prod]
    have hshift : ∀ j, σ ((σ ^ j : L ≃+* L) x) = (σ ^ (j + 1) : L ≃+* L) x := by
      intro j
      rw [pow_succ' σ j]
      rfl
    calc x * ∏ j ∈ Finset.range i, σ ((σ ^ j : L ≃+* L) x)
        = x * ∏ j ∈ Finset.range i, (σ ^ (j + 1) : L ≃+* L) x := by
          refine congrArg (x * ·) (Finset.prod_congr rfl fun j _ => hshift j)
      _ = ∏ j ∈ Finset.range (i + 1), (σ ^ j : L ≃+* L) x := by
          rw [Finset.prod_range_succ']
          rw [pow_zero]
          rw [mul_comm]
          rfl
  set χ : ℕ → (Lˣ →* L) :=
    fun i => (((σ ^ i : L ≃+* L) : L →+* L).toMonoidHom.comp (Units.coeHom L)) with hχ
  have hχinj : Set.InjOn χ (Finset.range n) := pow_apply_units_injOn σ hord
  have hinj : Function.Injective (fun i : Fin n => χ (i : ℕ)) := by
    have hmem : ∀ k : Fin n, (k : ℕ) ∈ (Finset.range n : Set ℕ) := fun k => by
      rw [Finset.coe_range]; exact Set.mem_Iio.mpr k.isLt
    intro i j hij
    exact Fin.ext (hχinj (hmem i) (hmem j) hij)
  have hLI : LinearIndependent L (fun i : Fin n => ⇑(χ (i : ℕ))) :=
    (linearIndependent_monoidHom Lˣ L).comp (fun i : Fin n => χ (i : ℕ)) hinj
  have hnonzero : (∑ i : Fin n, a (i : ℕ) • ⇑(χ (i : ℕ))) ≠ 0 := by
    intro hzero
    have h0 := Fintype.linearIndependent_iff.mp hLI (fun i : Fin n => a (i : ℕ)) hzero
    have hn' : (0 : ℕ) < n := hn0
    have := h0 ⟨0, hn'⟩
    exact hane 0 this
  obtain ⟨c, hc⟩ : ∃ c : Lˣ, (∑ i : Fin n, a (i : ℕ) • ⇑(χ (i : ℕ))) c ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hnonzero (funext fun c => hall c)
  set b : L := ∑ i ∈ Finset.range n, a i * (σ ^ i : L ≃+* L) (c : L) with hb
  have hbc : (∑ i : Fin n, a (i : ℕ) • ⇑(χ (i : ℕ))) c = b := by
    rw [hb, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Fin.sum_univ_eq_sum_range (fun i => a i * (χ i) c)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hχ]
  have hbne : b ≠ 0 := by rw [← hbc]; exact hc
  refine ⟨b, hbne, ?_⟩
  have hσn : (σ ^ n : L ≃+* L) = 1 := by rw [← hord]; exact pow_orderOf_eq_one σ
  calc x * σ b
      = ∑ i ∈ Finset.range n, x * σ (a i) * (σ ^ (i + 1) : L ≃+* L) (c : L) := by
        rw [hb, map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul]
        have hshift : σ ((σ ^ i : L ≃+* L) (c : L)) = (σ ^ (i + 1) : L ≃+* L) (c : L) := by
          rw [pow_succ' σ i]; rfl
        rw [hshift, mul_assoc]
    _ = ∑ i ∈ Finset.range n, a (i + 1) * (σ ^ (i + 1) : L ≃+* L) (c : L) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [haS i]
    _ = ∑ i ∈ Finset.range (n + 1), a i * (σ ^ i : L ≃+* L) (c : L)
          - a 0 * (σ ^ 0 : L ≃+* L) (c : L) := by
        rw [Finset.sum_range_succ' (fun i => a i * (σ ^ i : L ≃+* L) (c : L)) n]
        ring
    _ = b + a n * (σ ^ n : L ≃+* L) (c : L) - a 0 * (σ ^ 0 : L ≃+* L) (c : L) := by
        rw [Finset.sum_range_succ, hb]
    _ = b := by
        rw [haN, ha0, hσn, pow_zero]
        simp

end CyclicHilbert90
end M4aLocalCFT

open _root_.M4aLocalCFT _root_.P2MW.S_M4aLocalCFT_fieldUnitsDecomp_norm_ker_le_derive_range.M4aLocalCFT in
theorem solution {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)
    [Finite (A.decompositionSubgroup K)]
    (g : A.decompositionSubgroup K) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    (M4aLocalCFT.fieldUnitsNorm (K := K) A).ker ≤
      (M4aLocalCFT.fieldUnitsDerive A g).range := by
  classical
  intro x hx
  letI := Fintype.ofFinite (A.decompositionSubgroup K)

  let φ : (L ≃ₐ[K] L) →* (L ≃+* L) :=
    { toFun := AlgEquiv.toRingEquiv, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hφinj : Function.Injective φ :=
    fun a b hab => AlgEquiv.ext (fun z => RingEquiv.congr_fun hab z)
  set σ : L ≃+* L := φ (g : L ≃ₐ[K] L) with hσdef

  have hordg : orderOf g = Nat.card (A.decompositionSubgroup K) :=
    orderOf_eq_card_of_forall_mem_zpowers hg
  have hordg1 : orderOf (g : L ≃ₐ[K] L) = orderOf g :=
    orderOf_injective (A.decompositionSubgroup K).subtype
      (Subgroup.subtype_injective _) g
  have hordσ : orderOf σ = orderOf g := by
    rw [hσdef]
    exact (orderOf_injective φ hφinj (g : L ≃ₐ[K] L)).trans hordg1
  have hn0 : 0 < orderOf g := by rw [hordg]; exact Nat.card_pos

  have hσpow : ∀ i : ℕ, (σ ^ i : L ≃+* L) = ((g : L ≃ₐ[K] L) ^ i).toRingEquiv := by
    intro i; rw [hσdef]; exact (φ.map_pow (g : L ≃ₐ[K] L) i).symm
  have hcoe : ∀ i : ℕ, ((g ^ i : A.decompositionSubgroup K) : L ≃ₐ[K] L)
      = (g : L ≃ₐ[K] L) ^ i :=
    fun i => (A.decompositionSubgroup K).subtype.map_pow g i

  have hact : ∀ (i : ℕ) (y : Lˣ),
      ((fieldUnitsAct A (g ^ i) y : Lˣ) : L) = (σ ^ i : L ≃+* L) (y : L) := by
    intro i y
    show (((g^i : A.decompositionSubgroup K) : L ≃ₐ[K] L) : L → L) (y : L) = _
    rw [hcoe i, hσpow i]; rfl

  have hNx : ∏ i ∈ Finset.range (orderOf g), (σ ^ i : L ≃+* L) (x : L) = 1 := by
    have hx1 : fieldUnitsNorm (K := K) A x = 1 := hx
    have hx2 : (∏ s : A.decompositionSubgroup K, fieldUnitsAct A s) x = 1 := hx1
    rw [MonoidHom.finsetProd_apply] at hx2
    have hreidx : ∏ s : A.decompositionSubgroup K, fieldUnitsAct A s x
        = ∏ i ∈ Finset.range (orderOf g), fieldUnitsAct A (g ^ i) x := by
      refine (Finset.prod_bij (fun i _ => g ^ i) (fun i hi => Finset.mem_univ _) ?_ ?_
        (fun i hi => rfl)).symm
      · intro i hi j hj hij
        exact pow_injOn_Iio_orderOf (by simpa using Finset.mem_range.mp hi)
          (by simpa using Finset.mem_range.mp hj) hij
      · intro s _
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp
          ((mem_zpowers_iff_mem_range_orderOf (x := g) (y := s)).mp (hg s))
        exact ⟨i, by simpa using hi, rfl⟩
    rw [hreidx] at hx2
    calc ∏ i ∈ Finset.range (orderOf g), (σ ^ i : L ≃+* L) (x : L)
        = ((∏ i ∈ Finset.range (orderOf g), fieldUnitsAct A (g ^ i) x : Lˣ) : L) := by
          rw [Units.coe_prod]
          exact Finset.prod_congr rfl fun i _ => (hact i x).symm
      _ = 1 := by rw [hx2]; rfl

  obtain ⟨b, hbne, hbeq⟩ :=
    M4aLocalCFT.CyclicHilbert90.exists_mul_map_eq_of_prod_pow_eq_one σ hn0 hordσ
      (x : L) x.ne_zero hNx

  refine ⟨(Units.mk0 b hbne)⁻¹, ?_⟩
  apply Units.ext
  have hderiv : fieldUnitsDerive A g (Units.mk0 b hbne)⁻¹
      = fieldUnitsAct A g (Units.mk0 b hbne)⁻¹ / (Units.mk0 b hbne)⁻¹ := by
    simp only [fieldUnitsDerive, MonoidHom.div_apply, MonoidHom.id_apply]
  rw [hderiv, Units.val_div_eq_div_val]
  have hg1act : ((fieldUnitsAct A g (Units.mk0 b hbne)⁻¹ : Lˣ) : L) = σ b⁻¹ := by
    have h := hact 1 (Units.mk0 b hbne)⁻¹
    rw [pow_one] at h
    simpa using h
  rw [hg1act, Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀]
  have hσbne : σ b ≠ 0 := (map_ne_zero σ).mpr hbne
  rw [inv_div_inv, div_eq_iff hσbne]
  exact hbeq.symm

#check @solution
#print axioms solution

end S_M4aLocalCFT_fieldUnitsDecomp_norm_ker_le_derive_range
end P2MW
export P2MW.S_M4aLocalCFT_fieldUnitsDecomp_norm_ker_le_derive_range (solution)
