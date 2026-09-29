-- Prove2me | solution 1 for ModularCurve.exists_addMonoidHom_torsion_recipe_qExpansionDiffAlong_congr_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/7baaf1b7-a842-5131-ba57-c2995924d344

import Mathlib
import Definitions.Def_AlgebraicCurve_Pic0Congr
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_ModularCurve_QExpansionDiff
import Theorems.Thm_ModularCurve_eq_qExpansionDiffAlong_of_isQExpansionDiffAlong
import Theorems.Thm_ModularCurve_isQExpansionDiffAlong_qExpansionDiffAlong
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_addMonoidHom_torsion_recipe_qExpansionDiffAlong_congr_eq

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open AlgebraicCurve ModularCurve

theorem solution
    (K : Type*) [Field K] (p : ℕ)
    {F₁ F₂ : IntermediateField K (LaurentSeries K)} (hE : F₁ = F₂)
    (δ₁ : Pic0.torsion K F₁ p →+ Ω[↥F₁⁄K])
    (hδ₁ : ∀ (y : Pic0.torsion K F₁ p) (E : Divisor.degZero (K := K) (F := ↥F₁)) (g : ↥F₁),
        Pic0.mk E = (y : Pic0 K F₁) → g ≠ 0 →
        (∀ v : Place K F₁, (p : ℤ) * (E : Divisor K F₁) v = v.ord g) →
        δ₁ y = g⁻¹ • KaehlerDifferential.D K (↥F₁) g) :
    ∃ (τ : Pic0.torsion K F₁ p ≃+ Pic0.torsion K F₂ p)
      (δ₂ : Pic0.torsion K F₂ p →+ Ω[↥F₂⁄K]),
      (∀ x : Pic0.torsion K F₁ p, ((τ x : Pic0.torsion K F₂ p) : Pic0 K F₂) =
        Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv
          (fun a => (IntermediateField.equivOfEq hE).commutes a) (x : Pic0 K F₁)) ∧
      (∀ (y : Pic0.torsion K F₂ p) (E : Divisor.degZero (K := K) (F := ↥F₂)) (g : ↥F₂),
        Pic0.mk E = (y : Pic0 K F₂) → g ≠ 0 →
        (∀ v : Place K F₂, (p : ℤ) * (E : Divisor K F₂) v = v.ord g) →
        δ₂ y = g⁻¹ • KaehlerDifferential.D K (↥F₂) g) ∧
      (∀ x : Pic0.torsion K F₁ p,
        qExpansionDiffAlong F₂.val (δ₂ (τ x)) = qExpansionDiffAlong F₁.val (δ₁ x)) := by
  classical
  subst hE

  set ea : ↥F₁ ≃ₐ[K] ↥F₁ := IntermediateField.equivOfEq (rfl : F₁ = F₁) with hea
  set e : ↥F₁ ≃+* ↥F₁ := ea.toRingEquiv with hedef
  have he : ∀ a : K, e (algebraMap K F₁ a) = algebraMap K F₁ a := fun a => ea.commutes a
  have hea_apply : ∀ x : ↥F₁, ea x = x := fun x => Subtype.ext rfl
  have he_apply : ∀ x : ↥F₁, e x = x := hea_apply
  have hea_apply' : ∀ x : ↥F₁, (ea : ↥F₁ →ₐ[K] ↥F₁) x = x := fun x => Subtype.ext rfl
  set cg : Pic0 K F₁ ≃+ Pic0 K F₁ := Pic0.congr e he with hcg
  have hcg_mk : ∀ D : Divisor.degZero (K := K) (F := ↥F₁),
      cg (Pic0.mk D) = Pic0.mk (Pic0.degZeroCongr e he D) := fun D => rfl

  have hmem : ∀ x : Pic0 K F₁, x ∈ Pic0.torsion K F₁ p ↔ cg x ∈ Pic0.torsion K F₁ p := by
    intro x
    rw [Pic0.mem_torsion, Pic0.mem_torsion, ← map_zsmul, AddEquiv.map_eq_zero_iff]
  let τ : Pic0.torsion K F₁ p ≃+ Pic0.torsion K F₁ p :=
    { toFun := fun x => ⟨cg x, (hmem x).mp x.2⟩
      invFun := fun y => ⟨cg.symm y, by
        have h := (hmem (cg.symm y)).mpr
        rw [AddEquiv.apply_symm_apply] at h
        exact h y.2⟩
      left_inv := fun x => Subtype.ext (cg.symm_apply_apply x)
      right_inv := fun y => Subtype.ext (cg.apply_symm_apply y)
      map_add' := fun x y => Subtype.ext (map_add cg (x : Pic0 K F₁) (y : Pic0 K F₁)) }
  have hτ : ∀ x : Pic0.torsion K F₁ p, ((τ x : Pic0.torsion K F₁ p) : Pic0 K F₁) = cg x := fun _ => rfl
  have hτs : ∀ y : Pic0.torsion K F₁ p, ((τ.symm y : Pic0.torsion K F₁ p) : Pic0 K F₁) = cg.symm y :=
    fun _ => rfl

  let δ₂ : Pic0.torsion K F₁ p →+ Ω[↥F₁⁄K] :=
    (Differential.pullbackAlong ea.toAlgHom).toAddMonoidHom.comp (δ₁.comp τ.symm.toAddMonoidHom)
  have hδ₂_apply : ∀ y, δ₂ y = Differential.pullbackAlong ea.toAlgHom (δ₁ (τ.symm y)) := fun _ => rfl
  refine ⟨τ, δ₂, hτ, ?_, ?_⟩
  ·
    intro y E g hEy hg0 hpE
    set E₁ : Divisor.degZero (K := K) (F := ↥F₁) := (Pic0.degZeroCongr e he).symm E with hE₁
    have hx : Pic0.mk E₁ = ((τ.symm y : Pic0.torsion K F₁ p) : Pic0 K F₁) := by
      rw [hτs, ← hEy]
      apply cg.injective
      rw [AddEquiv.apply_symm_apply, hcg_mk, hE₁, AddEquiv.apply_symm_apply]
    have hg1 : e.symm g ≠ 0 := fun h0 => hg0 (by simpa using congrArg e h0)
    have hpE₁ : ∀ v : Place K F₁, (p : ℤ) * (E₁ : Divisor K F₁) v = v.ord (e.symm g) := by
      intro v
      rw [hE₁, Pic0.coe_degZeroCongr_symm, Divisor.congr_symm_apply_place,
        ← Place.ord_congrRingEquiv e he v (e.symm g), RingEquiv.apply_symm_apply]
      exact hpE _
    have h1 : δ₁ (τ.symm y) = (e.symm g)⁻¹ • KaehlerDifferential.D K (↥F₁) (e.symm g) :=
      hδ₁ _ E₁ (e.symm g) hx hg1 hpE₁
    rw [hδ₂_apply, h1, Differential.pullbackAlong_smul, Differential.pullbackAlong_D]
    have : ea.toAlgHom (e.symm g) = g := by
      show e (e.symm g) = g
      exact e.apply_symm_apply g
    rw [map_inv₀, this]
  ·
    intro x
    rw [hδ₂_apply]
    have hcomp : (qExpansionDiffAlong F₁.val) ∘ₗ (Differential.pullbackAlong ea.toAlgHom) =
        qExpansionDiffAlong F₁.val := by
      apply eq_qExpansionDiffAlong_of_isQExpansionDiffAlong
      obtain ⟨hD, hsm⟩ := isQExpansionDiffAlong_qExpansionDiffAlong (F₁.val)
      refine ⟨fun z => ?_, fun f ω => ?_⟩
      · rw [LinearMap.comp_apply, Differential.pullbackAlong_D, hD]
        rfl
      · rw [LinearMap.comp_apply, Differential.pullbackAlong_smul, hsm]
        rfl
    have := congrArg (fun φ => φ (δ₁ (τ.symm (τ x)))) hcomp
    simp only [LinearMap.comp_apply, AddEquiv.symm_apply_apply] at this
    rw [AddEquiv.symm_apply_apply]
    exact this

end S_ModularCurve_exists_addMonoidHom_torsion_recipe_qExpansionDiffAlong_congr_eq
end P2MW
export P2MW.S_ModularCurve_exists_addMonoidHom_torsion_recipe_qExpansionDiffAlong_congr_eq (solution)
