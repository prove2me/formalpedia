-- Prove2me | solution 1 for NeronModelInfra.TopFormOrder.integralTopForms_eq_span_and_ord_smul_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/b14300e5-1680-552a-b047-d5b43aa0c2f1

import Mathlib
import Definitions.Def_NeronModelInfra_TopFormOrder
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_TopFormOrder_integralTopForms_eq_span_and_ord_smul_of_basis

set_option autoImplicit false

universe u

open NeronModelInfra.TopFormOrder

namespace OCBTop

open Set Set.powersetCard

@[reducible] noncomputable def uniquePowersetCardFin (n : ℕ) : Unique (Set.powersetCard (Fin n) n) where
  default := Set.powersetCard.ofCard (n := n) (s := (Finset.univ : Finset (Fin n))) (by simp)
  uniq s := Subtype.ext (Finset.eq_univ_of_card _ (by
    rw [Fintype.card_fin]; exact Set.powersetCard.card_eq s))

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M] {n : ℕ}

lemma exists_basis_exteriorPower_top (b : Module.Basis (Fin n) A M) :
    ∃ B : Module.Basis (Set.powersetCard (Fin n) n) A (⋀[A]^n M), ∀ s, B s = exteriorPower.ιMulti A n b := by
  letI := uniquePowersetCardFin n
  let φ : Fin n ↪o Fin n := ofFinEmbEquiv.symm (default : Set.powersetCard (Fin n) n)
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective φ (Finite.injective_iff_bijective.1 φ.injective)
  refine ⟨(b.reindex σ).exteriorPower n, fun s => ?_⟩
  rw [Subsingleton.elim s default, exteriorPower.basis_apply]
  change exteriorPower.ιMulti A n ((b.reindex σ) ∘ σ) = _
  congr 1
  funext i
  simp

lemma exists_eq_smul_ιMulti (b : Module.Basis (Fin n) A M) (x : ⋀[A]^n M) :
    ∃ r : A, x = r • exteriorPower.ιMulti A n b := by
  letI := uniquePowersetCardFin n
  obtain ⟨B, hB⟩ := exists_basis_exteriorPower_top b
  refine ⟨B.repr x default, ?_⟩
  conv_lhs => rw [← B.sum_repr x]
  rw [Fintype.sum_unique, hB]

end OCBTop

namespace OCA
open NeronModelInfra.TopFormOrder IsDedekindDomain

variable (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (L : Type u) [Field L] [Algebra O L] [IsFractionRing O L]

lemma addOrd_of_ne_zero {a : L} (ha : a ≠ 0) :
    addOrd O L a = -(Multiplicative.toAdd (WithZero.unzero
      (((maximalSpectrum O).valuation L).ne_zero_iff.mpr ha))) := by
  unfold addOrd; rw [dif_neg ha]

lemma addOrd_mul {a b : L} (ha : a ≠ 0) (hb : b ≠ 0) :
    addOrd O L (a * b) = addOrd O L a + addOrd O L b := by
  rw [addOrd_of_ne_zero O L ha, addOrd_of_ne_zero O L hb, addOrd_of_ne_zero O L (mul_ne_zero ha hb),
    ← neg_add, ← toAdd_mul]
  congr 2
  apply WithZero.coe_injective
  rw [WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_unzero, WithZero.coe_unzero, map_mul]

lemma unzero_le_one {x : O} (hx : x ≠ 0) :
    WithZero.unzero (((maximalSpectrum O).valuation L).ne_zero_iff.mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective O L)).mpr hx)) ≤ 1 := by
  rw [← WithZero.coe_le_coe, WithZero.coe_unzero, WithZero.coe_one,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  exact (maximalSpectrum O).intValuation_le_one x

lemma addOrd_algebraMap_nonneg (x : O) : 0 ≤ addOrd O L (algebraMap O L x) := by
  by_cases hx : x = 0
  · subst hx; unfold addOrd; simp
  have hne : algebraMap O L x ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O L)).mpr hx
  rw [addOrd_of_ne_zero O L hne, neg_nonneg]
  have h := unzero_le_one O L hx
  rw [← Multiplicative.toAdd_le, toAdd_one] at h
  exact h

lemma addOrd_algebraMap_eq_zero_iff {x : O} (hx : x ≠ 0) :
    addOrd O L (algebraMap O L x) = 0 ↔ IsUnit x := by
  have hne : algebraMap O L x ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O L)).mpr hx
  rw [addOrd_of_ne_zero O L hne, neg_eq_zero]
  constructor
  · intro h
    have h1 : (maximalSpectrum O).valuation L (algebraMap O L x) = 1 := by
      rw [← WithZero.coe_unzero (((maximalSpectrum O).valuation L).ne_zero_iff.mpr hne), ← WithZero.coe_one,
        Multiplicative.toAdd.injective (h.trans toAdd_one.symm)]
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff] at h1
    by_contra hu
    exact h1 ((IsLocalRing.mem_maximalIdeal x).mpr hu)
  · intro hu
    have h1 : (maximalSpectrum O).intValuation x = 1 :=
      IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr
        (fun hm => (IsLocalRing.mem_maximalIdeal x).mp hm hu)
    have h2 : WithZero.unzero (((maximalSpectrum O).valuation L).ne_zero_iff.mpr hne) = 1 := by
      apply WithZero.coe_injective
      rw [WithZero.coe_unzero, WithZero.coe_one, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, h1]
    rw [h2, toAdd_one]

end OCA

set_option maxHeartbeats 3200000 in
theorem solution
    (R' K' O F : Type u) [CommRing R'] [CommRing K'] [Algebra R' K']
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra R' O]
    [Field F] [Algebra O F] [IsFractionRing O F] [Algebra K' F] [Algebra R' F]
    [IsScalarTower R' O F] [IsScalarTower R' K' F]
    (d : ℕ) (b : Module.Basis (Fin d) O (Ω[O⁄R'])) :
    letI := moduleAlong O F (⋀[F]^d (Ω[F⁄K']))
    integralTopForms R' K' O F d =
        Submodule.span O {topFormMap R' K' O F d (exteriorPower.ιMulti O d b)} ∧
      ∀ a : F, a ≠ 0 → topFormMap R' K' O F d (exteriorPower.ιMulti O d b) ≠ 0 →
        ord R' K' O d F (a • topFormMap R' K' O F d (exteriorPower.ιMulti O d b)) = addOrd O F a := by
  classical
  letI inst := moduleAlong O F (⋀[F]^d (Ω[F⁄K']))

  have h1 : integralTopForms R' K' O F d =
      Submodule.span O {topFormMap R' K' O F d (exteriorPower.ιMulti O d b)} := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      obtain ⟨r, rfl⟩ := OCBTop.exists_eq_smul_ιMulti b x
      rw [map_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact ⟨_, rfl⟩
  refine ⟨h1, ?_⟩
  intro a ha hρ

  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ⋀[F]^d (Ω[F⁄K']), ρ = topFormMap R' K' O F d (exteriorPower.ιMulti O d b) := ⟨_, rfl⟩
  rw [← hρdef] at h1 hρ ⊢
  have hex : ∃ ρ' : ⋀[F]^d (Ω[F⁄K']), integralTopForms R' K' O F d = Submodule.span O {ρ'} ∧
      ∃ a' : F, a • ρ = a' • ρ' := ⟨ρ, h1, a, rfl⟩

  show (if h : ∃ ρ' : ⋀[F]^d (Ω[F⁄K']), integralTopForms R' K' O F d = Submodule.span O {ρ'} ∧
      ∃ a' : F, a • ρ = a' • ρ' then addOrd O F h.choose_spec.2.choose else 0) = addOrd O F a
  rw [dif_pos hex]

  have hΛ₁ : integralTopForms R' K' O F d = Submodule.span O {hex.choose} := hex.choose_spec.1
  have hω₁ : a • ρ = hex.choose_spec.2.choose • hex.choose := hex.choose_spec.2.choose_spec

  have hspan : Submodule.span O {ρ} = Submodule.span O {hex.choose} := h1.symm.trans hΛ₁
  obtain ⟨c, hc⟩ : ∃ c : O, c • ρ = hex.choose :=
    Submodule.mem_span_singleton.mp (hspan.ge (Submodule.mem_span_singleton_self _))
  obtain ⟨c', hc'⟩ : ∃ c' : O, c' • hex.choose = ρ :=
    Submodule.mem_span_singleton.mp (hspan.le (Submodule.mem_span_singleton_self _))

  have hsmul : ∀ (r : O) (v : ⋀[F]^d (Ω[F⁄K'])), r • v = algebraMap O F r • v := fun r v => rfl
  have hinj : Function.Injective fun x : F => x • ρ := smul_left_injective F hρ

  have hcc : c' * c = 1 := by
    apply IsFractionRing.injective O F
    rw [map_one]
    apply hinj
    show algebraMap O F (c' * c) • ρ = (1 : F) • ρ
    rw [one_smul, map_mul, mul_smul, ← hsmul c, hc, ← hsmul, hc']
  have hcu : IsUnit c := ⟨⟨c, c', by rw [mul_comm]; exact hcc, hcc⟩, rfl⟩
  have hc0 : c ≠ 0 := hcu.ne_zero

  have haeq : a = hex.choose_spec.2.choose * algebraMap O F c := by
    apply hinj
    show a • ρ = (hex.choose_spec.2.choose * algebraMap O F c) • ρ
    rw [mul_smul, ← hsmul, hc, ← hω₁]
  have ha₁ : hex.choose_spec.2.choose ≠ 0 := by
    intro h0; apply ha; rw [haeq, h0, zero_mul]
  have hcF : algebraMap O F c ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O F)).mpr hc0
  conv_rhs => rw [haeq]
  rw [OCA.addOrd_mul O F ha₁ hcF, (OCA.addOrd_algebraMap_eq_zero_iff O F hc0).mpr hcu, add_zero]

end S_NeronModelInfra_TopFormOrder_integralTopForms_eq_span_and_ord_smul_of_basis
end P2MW
export P2MW.S_NeronModelInfra_TopFormOrder_integralTopForms_eq_span_and_ord_smul_of_basis (solution)
