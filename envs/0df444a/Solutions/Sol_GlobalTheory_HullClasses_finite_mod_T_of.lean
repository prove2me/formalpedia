-- Prove2me | solution 1 for GlobalTheory.HullClasses.finite_mod_T_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:09:44.592119+00:00
-- url     : https://prove2.me/submissions/56b6a9f6-83f6-4906-a228-3e6020f19ea0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntUnitOfMulLat
import Theorems.Thm_GlobalTheory_HullClasses_mulLat_mul
import Theorems.Thm_GlobalTheory_HullClasses_mulLat_one
import Theorems.Thm_GlobalTheory_HullClasses_mulLat_le_mul
import Theorems.Thm_GlobalTheory_HullClasses_mulLat_intUnit
import Theorems.Thm_GlobalTheory_HullClasses_intUnit_of_mulLat
import Theorems.Thm_GlobalTheory_HullClasses_isLat_mulLat
import Theorems.Thm_GlobalTheory_HullClasses_sigma_algebraMap
import Theorems.Thm_GlobalTheory_HullClasses_key

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
noncomputable section
noncomputable section
open GlobalTheory GlobalTheory.HullClasses
namespace GlobalTheory.HullClasses
theorem _root_.solution (K : UQ) (B : InvAlg K)
    (hPr : ∀ J : Submodule K.O B.A, IsLat K.O K.E J → (∀ a ∈ integralClosure K.O B.A, ∀ y ∈ J, a * y ∈ J) →
      ∃ a : B.Aˣ, J = mulLat K.O (a : B.A) (Subalgebra.toSubmodule (integralClosure K.O B.A)))
    (hNu : ∃ F : Finset B.Aˣ, ∀ u : B.Aˣ, (∃ w ∈ intUnits K.O B.A, (w : B.A) = u * B.σ u) →
      ∃ f ∈ F, ∃ t ∈ B.T, u * f⁻¹ * t⁻¹ ∈ intUnits K.O B.A)
    (hBe : ∀ (L : Submodule K.O B.A), IsLat K.O K.E L → ∀ c : K.O, c ≠ 0 →
      {M : Submodule K.O B.A | mulLat K.O (algebraMap K.O B.A c) L ≤ M ∧ M ≤ L}.Finite)
    (x : B.A) (c : K.O) (hc0 : c ≠ 0) :
    ∃ S : Set (Submodule K.O B.A), S.Finite ∧ (∀ J ∈ S, IsLat K.O K.E J) ∧
      ∀ J : Submodule K.O B.A, IsLat K.O K.E J → (∀ a ∈ integralClosure K.O B.A, ∀ y ∈ J, a * y ∈ J) →
        (∀ y, (∀ z ∈ J, B.herm x y z ∈ (algebraMap K.O K.E).range) → y ∈ J) →
        (∀ y ∈ J, ∀ z ∈ J, B.herm x (algebraMap K.O B.A c * y) (algebraMap K.O B.A c * z) ∈
          (algebraMap K.O K.E).range) →
        ∃ t ∈ B.T, mulLat K.O (t : B.A) J ∈ S := by
  classical
  obtain ⟨cb, hcb⟩ := K.c_int c
  have hσc := sigma_algebraMap B c cb hcb
  have hcb0 : cb ≠ 0 := by
    rintro rfl
    rw [map_zero, map_eq_zero_iff _ K.c.injective] at hcb
    exact hc0 ((IsFractionRing.injective K.O K.E) (by rw [hcb, map_zero]))
  set d : K.O := c * cb with hd
  have hd0 : d ≠ 0 := mul_ne_zero hc0 hcb0
  have hdd0 : d * d ≠ 0 := mul_ne_zero hd0 hd0
  have hDu : IsUnit (algebraMap K.O B.A d) := by
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A]
    refine (IsUnit.mk0 _ ?_).map _
    rw [Ne, ← map_zero (algebraMap K.O K.E)]
    exact (IsFractionRing.injective K.O K.E).ne hd0
  set D : B.Aˣ := hDu.unit
  have hDc : (D : B.A) = algebraMap K.O B.A d := hDu.unit_spec
  let σU : B.Aˣ →* B.Aˣ := Units.map B.σ.toMonoidHom
  have hσU : ∀ a : B.Aˣ, ((σU a : B.Aˣ) : B.A) = B.σ (a : B.A) := fun a => rfl
  let Nu : B.Aˣ → B.Aˣ := fun a => a * σU a
  have hNuc : ∀ a, ((Nu a : B.Aˣ) : B.A) = (a : B.A) * B.σ (a : B.A) := fun a => by simp [Nu, hσU]
  let Λ := abelian₂ B
  let adm : B.Aˣ → Prop := fun a =>
    (∀ y, (∀ z ∈ mulLat K.O (a : B.A) Λ, B.herm x y z ∈ (algebraMap K.O K.E).range) →
      y ∈ mulLat K.O (a : B.A) Λ) ∧
    (∀ y ∈ mulLat K.O (a : B.A) Λ, ∀ z ∈ mulLat K.O (a : B.A) Λ,
      B.herm x (algebraMap K.O B.A c * y) (algebraMap K.O B.A c * z) ∈ (algebraMap K.O K.E).range)
  by_cases hex : ∃ a₀ : B.Aˣ, IsLat K.O K.E (mulLat K.O (a₀ : B.A) Λ) ∧ adm a₀
  swap
  · refine ⟨∅, Set.finite_empty, by simp, ?_⟩
    intro J hJ hst h3 h4
    obtain ⟨a, rfl⟩ := hPr J hJ hst
    exact (hex ⟨a, hJ, h3, h4⟩).elim
  obtain ⟨a₀, hJ₀, hadm₀⟩ := hex
  have hΛ : IsLat K.O K.E Λ := by
    have := isLat_mulLat B a₀⁻¹ hJ₀
    rwa [← mulLat_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, mulLat_one] at this
  let Mf : B.Aˣ → Submodule K.O B.A := fun a => mulLat K.O ((D * Nu a * (Nu a₀)⁻¹ : B.Aˣ) : B.A) Λ
  let Bset := {M : Submodule K.O B.A | mulLat K.O (algebraMap K.O B.A (d * d)) Λ ≤ M ∧ M ≤ Λ}
  have hcancel : ∀ a : B.Aˣ, mulLat K.O (((a⁻¹ : B.Aˣ) : B.A) * a) Λ = Λ := fun a => by
    rw [Units.inv_mul, mulLat_one]
  have hM : ∀ a, adm a → Mf a ∈ Bset := by
    intro a ha
    have k1 := key B x c cb hσc a a₀ ha.2 hadm₀.1
    have k2 := key B x c cb hσc a₀ a hadm₀.2 ha.1
    constructor
    · have := mulLat_le_mul (((D * (Nu a₀)⁻¹ : B.Aˣ) : B.A)) _ _ Λ k2
      convert this using 2
      · rw [map_mul, ← hDc, ← hNuc]
        simp only [Units.val_mul]
        calc (D : B.A) * D = D * D * (((Nu a₀)⁻¹ : B.Aˣ) * (Nu a₀ : B.A)) := by rw [Units.inv_mul, mul_one]
          _ = _ := by ring
      · rw [← hNuc]; simp only [Units.val_mul, Mf]; ring
    · have := mulLat_le_mul ((((Nu a₀)⁻¹ : B.Aˣ)) : B.A) _ _ Λ k1
      rw [← hNuc, ← hNuc, hcancel] at this
      convert this using 2
      simp only [Units.val_mul]; rw [hDc, hd]; ring
  let gch : Submodule K.O B.A → B.Aˣ := fun M => if h : ∃ a, adm a ∧ Mf a = M then h.choose else 1
  obtain ⟨F, hF⟩ := hNu
  refine ⟨(fun p : Submodule K.O B.A × B.Aˣ => mulLat K.O ((gch p.1 * p.2 : B.Aˣ) : B.A) Λ) ''
    (Bset ×ˢ (F : Set B.Aˣ)), ((hBe Λ hΛ (d * d) hdd0).prod F.finite_toSet).image _, ?_, ?_⟩
  · rintro J ⟨p, -, rfl⟩
    exact isLat_mulLat B _ hΛ
  intro J hJ hst h3 h4
  obtain ⟨a, rfl⟩ := hPr J hJ hst
  have ha : adm a := ⟨h3, h4⟩
  have hex' : ∃ a', adm a' ∧ Mf a' = Mf a := ⟨a, ha, rfl⟩
  have hg : gch (Mf a) = hex'.choose := dif_pos hex'
  obtain ⟨ha', hMa'⟩ := hex'.choose_spec
  set a' := hex'.choose

  have hv : Nu a * (Nu a')⁻¹ ∈ intUnits K.O B.A := by
    apply intUnit_of_mulLat
    have e1 : ((Nu a * (Nu a')⁻¹ : B.Aˣ) : B.A) =
        (((D * Nu a' * (Nu a₀)⁻¹)⁻¹ : B.Aˣ) : B.A) * ((D * Nu a * (Nu a₀)⁻¹ : B.Aˣ) : B.A) := by
      rw [← Units.val_mul]; congr 1; (apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel)
    rw [e1, mulLat_mul]
    change mulLat K.O _ (Mf a) = Λ
    rw [← hMa']
    change mulLat K.O _ (mulLat K.O _ Λ) = Λ
    rw [← mulLat_mul, hcancel]
  set u : B.Aˣ := a * a'⁻¹
  have hu : ∃ w ∈ intUnits K.O B.A, (w : B.A) = u * B.σ u := by
    refine ⟨_, hv, ?_⟩
    rw [← hNuc]; congr 1; simp only [Nu, u, map_mul, map_inv]; (apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel)
  obtain ⟨f, hf, t, ht, hw⟩ := hF u hu
  refine ⟨t⁻¹, B.T.inv_mem ht, ⟨(Mf a, f), ⟨hM a ha, hf⟩, ?_⟩⟩
  have e2 : t⁻¹ * a = a' * f * (u * f⁻¹ * t⁻¹) := by simp only [u]; (apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel)
  show mulLat K.O ((gch (Mf a) * f : B.Aˣ) : B.A) Λ = mulLat K.O ((t⁻¹ : B.Aˣ) : B.A) (mulLat K.O (a : B.A) Λ)
  rw [hg, ← mulLat_mul, ← Units.val_mul, e2, Units.val_mul (a' * f), mulLat_mul _ _ Λ, mulLat_intUnit B _ hw]
end GlobalTheory.HullClasses
