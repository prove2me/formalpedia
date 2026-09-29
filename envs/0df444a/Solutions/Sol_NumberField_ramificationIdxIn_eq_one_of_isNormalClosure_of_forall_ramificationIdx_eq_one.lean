-- Prove2me | solution 1 for NumberField.ramificationIdxIn_eq_one_of_isNormalClosure_of_forall_ramificationIdx_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/1f18a4ed-ca8d-56aa-bd56-eebe77ec6bed

import Mathlib.NumberTheory.RamificationInertia.HilbertTheory
import Mathlib.RingTheory.Frobenius
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.GroupTheory.Perm.Sign
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_ramificationIdxIn_eq_one_of_isNormalClosure_of_forall_ramificationIdx_eq_one

set_option autoImplicit false

open IsDedekindDomain NumberField
open scoped Pointwise

namespace RamIdxNormalClosure

attribute [local instance] Ideal.Quotient.field

lemma conj_mem_inertia_smul {G B : Type*} [Group G] [CommRing B] [MulSemiringAction G B]
    (P : Ideal B) {σ : G} (hσ : σ ∈ P.inertia G) (g : G) :
    g⁻¹ * σ * g ∈ (g⁻¹ • P).inertia G := by
  intro x
  have h := Ideal.smul_mem_pointwise_smul g⁻¹ _ P (hσ (g • x))
  have hx : (g⁻¹ * σ * g) • x - x = g⁻¹ • (σ • (g • x) - g • x) := by
    rw [smul_sub, inv_smul_smul, mul_smul, mul_smul]
  simpa [hx] using h

noncomputable def resHom (E K L : Type*) [Field E] [Field K] [Field L]
    [Algebra E K] [Algebra E L] [Algebra K L] [IsScalarTower E K L] :
    (L ≃ₐ[K] L) →* (L ≃ₐ[E] L) where
  toFun τ := τ.restrictScalars E
  map_one' := AlgEquiv.ext fun _ => rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => rfl

lemma resHom_apply {E K L : Type*} [Field E] [Field K] [Field L]
    [Algebra E K] [Algebra E L] [Algebra K L] [IsScalarTower E K L] (τ : L ≃ₐ[K] L) (x : L) :
    resHom E K L τ x = τ x := rfl

lemma resHom_injective (E K L : Type*) [Field E] [Field K] [Field L]
    [Algebra E K] [Algebra E L] [Algebra K L] [IsScalarTower E K L] :
    Function.Injective (resHom E K L) :=
  AlgEquiv.restrictScalars_injective E

lemma apply_algebraMap_eq_of_mem_inertia
    (E K L : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra E K] [Algebra E L] [Algebra K L] [IsScalarTower E K L] [IsGalois E L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 E))
    (hK : ∀ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 E) = v →
      v.asIdeal.ramificationIdx' w.asIdeal = 1)
    (Q : Ideal (𝓞 L)) [Q.IsMaximal] [Q.LiesOver v.asIdeal]
    {σ : L ≃ₐ[E] L} (hσ : σ ∈ Q.inertia (L ≃ₐ[E] L)) (k : K) :
    σ (algebraMap K L k) = algebraMap K L k := by
  classical
  have hp : v.asIdeal ≠ ⊥ := v.ne_bot
  have hQ : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp Q

  let Qh : HeightOneSpectrum (𝓞 L) := ⟨Q, Ideal.IsMaximal.isPrime inferInstance, hQ⟩
  let w : HeightOneSpectrum (𝓞 K) := Qh.under (𝓞 K)
  have hw_as : w.asIdeal = Q.under (𝓞 K) := rfl
  have hwv : w.under (𝓞 E) = v := by
    apply HeightOneSpectrum.ext
    change (Q.under (𝓞 K)).under (𝓞 E) = v.asIdeal
    rw [Ideal.under_under]
    exact (Q.over_def v.asIdeal).symm
  have hw : w.asIdeal ≠ ⊥ := w.ne_bot
  haveI : Q.LiesOver w.asIdeal := ⟨rfl⟩
  haveI : w.asIdeal.LiesOver v.asIdeal := ⟨by
    change v.asIdeal = (w.under (𝓞 E)).asIdeal
    rw [hwv]⟩

  have he1 : v.asIdeal.ramificationIdx' w.asIdeal = 1 := hK w hwv
  have htower : v.asIdeal.ramificationIdx' Q = w.asIdeal.ramificationIdx' Q := by
    rw [Ideal.ramificationIdx_algebra_tower' v.asIdeal w.asIdeal Q, he1, one_mul]

  haveI : Finite ((𝓞 E) ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient hp
  haveI : Finite ((𝓞 K) ⧸ w.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient hw

  have hG : Nat.card (Q.inertia (L ≃ₐ[E] L)) = v.asIdeal.ramificationIdx' Q := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[E] L) v.asIdeal Q,
      Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal Q (L ≃ₐ[E] L),
      ← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal Q hp]
  have hH : Nat.card (Q.inertia (L ≃ₐ[K] L)) = w.asIdeal.ramificationIdx' Q := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) w.asIdeal Q,
      Ideal.ramificationIdxIn_eq_ramificationIdx w.asIdeal Q (L ≃ₐ[K] L),
      ← Ideal.ramificationIdx'_eq_ramificationIdx w.asIdeal Q hw]

  have hle : (Q.inertia (L ≃ₐ[K] L)).map (resHom E K L) ≤ Q.inertia (L ≃ₐ[E] L) := by
    rintro _ ⟨τ, hτ, rfl⟩ x
    have hτx := hτ x
    have hsm : (resHom E K L τ) • x = τ • x := by
      apply Subtype.ext
      rfl
    rw [hsm]
    exact hτx
  have heq : (Q.inertia (L ≃ₐ[K] L)).map (resHom E K L) = Q.inertia (L ≃ₐ[E] L) := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [Subgroup.card_map_of_injective (resHom_injective E K L), hG, hH, htower]
  have hσ' : σ ∈ (Q.inertia (L ≃ₐ[K] L)).map (resHom E K L) := heq ▸ hσ
  obtain ⟨τ, -, rfl⟩ := hσ'
  rw [resHom_apply]
  exact τ.commutes k

end RamIdxNormalClosure

attribute [local instance] Ideal.Quotient.field in
open RamIdxNormalClosure in
theorem solution
    (E K L : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra E K] [Algebra E L] [Algebra K L] [IsScalarTower E K L] [IsNormalClosure E K L]
    (v : HeightOneSpectrum (𝓞 E))
    (hK : ∀ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 E) = v → v.asIdeal.ramificationIdx' w.asIdeal = 1) :
    Ideal.ramificationIdxIn v.asIdeal (𝓞 L) = 1 := by
  classical

  haveI : Normal E L := IsNormalClosure.normal (K := K)
  haveI : IsGalois E L := ⟨⟩
  haveI : Normal K L := Normal.tower_top_of_normal E K L
  haveI : IsGalois K L := ⟨⟩
  have hp : v.asIdeal ≠ ⊥ := v.ne_bot

  obtain ⟨⟨P, hPp, hPo⟩⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 L)))
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp P
  haveI : P.IsMaximal := hPp.isMaximal hP0
  haveI : Finite ((𝓞 E) ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient hp

  suffices key : P.inertia (L ≃ₐ[E] L) = ⊥ by
    rw [← Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[E] L) v.asIdeal P, key,
      Subgroup.card_bot]
  refine (Subgroup.eq_bot_iff_forall _).mpr fun σ hσ => ?_

  have hfix : ∀ (g : L ≃ₐ[E] L) (k : K), σ (g (algebraMap K L k)) = g (algebraMap K L k) := by
    intro g k
    have hQp : (g⁻¹ • P) ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp (g⁻¹ • P)
    haveI : (g⁻¹ • P).IsMaximal := (Ideal.IsPrime.smul g⁻¹).isMaximal hQp
    have h := apply_algebraMap_eq_of_mem_inertia E K L v hK (g⁻¹ • P)
      (conj_mem_inertia_smul P hσ g) k
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv,
      AlgEquiv.symm_apply_eq] at h
    exact h

  apply AlgEquiv.ext
  intro y
  have htop : (⊤ : IntermediateField E L) ≤
      IntermediateField.fixedField (Subgroup.zpowers σ) := by
    rw [← IsNormalClosure.adjoin_rootSet (F := E) (K := K) (L := L)]
    refine iSup_le fun k => ?_
    rw [IntermediateField.adjoin_le_iff]
    intro r hr
    rw [Polynomial.mem_rootSet] at hr
    have halg : IsAlgebraic E (algebraMap K L k) := Algebra.IsAlgebraic.isAlgebraic _
    have hev : Polynomial.aeval r (minpoly E (algebraMap K L k)) = 0 := by
      rw [minpoly.algebraMap_eq (algebraMap K L).injective]
      exact hr.2
    obtain ⟨g, hg⟩ := minpoly.exists_algEquiv_of_root' halg hev
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro f hf
    have hσr : σ r = r := by rw [← hg]; exact hfix g k
    have hmem : f ∈ MulAction.stabilizer (L ≃ₐ[E] L) r :=
      (Subgroup.zpowers_le.mpr (by simpa [MulAction.mem_stabilizer_iff] using hσr)) hf
    simpa [MulAction.mem_stabilizer_iff] using hmem
  have hy : y ∈ IntermediateField.fixedField (Subgroup.zpowers σ) := htop IntermediateField.mem_top
  rw [IntermediateField.mem_fixedField_iff] at hy
  simpa using hy σ (Subgroup.mem_zpowers σ)

end S_NumberField_ramificationIdxIn_eq_one_of_isNormalClosure_of_forall_ramificationIdx_eq_one
end P2MW
export P2MW.S_NumberField_ramificationIdxIn_eq_one_of_isNormalClosure_of_forall_ramificationIdx_eq_one (solution)
