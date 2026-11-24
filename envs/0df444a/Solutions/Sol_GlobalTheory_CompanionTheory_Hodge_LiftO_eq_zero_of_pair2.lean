-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Hodge.LiftO.eq_zero_of_pair2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:44:56.666209+00:00
-- url     : https://prove2.me/submissions/b2e642fc-6d69-4893-ba7c-0d447f7a27fe

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExteriorPairingIotaTwo
import Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_LiftO_ext2
import Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_LiftO_wedge_basis_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_LiftO_wedge_basis_self_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_LiftO_wedge_basis_swap_neg
import Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_LiftO_exterior_pairing_iota_two
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hodge GlobalTheory.CompanionTheory.Hodge.LiftO
variable {R V W V' W' : Type} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  [AddCommGroup V'] [Module R V'] [AddCommGroup W'] [Module R W']
namespace GlobalTheory.CompanionTheory.Hodge.LiftO
theorem _root_.solution [Module.Finite R V] [Module.Projective R V] (t : ⋀[R]^2 V)
    (h : ∀ l u : V →ₗ[R] R, pair2 l u t = 0) : t = 0 := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R V
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  let c : Fin n → V →ₗ[R] R := fun i ↦ LinearMap.proj i ∘ₗ s
  let e : Fin n → V := fun i ↦ f (Pi.single i 1)
  have he : ∀ x, ∑ i, c i x • e i = x := fun x ↦ by
    have h1 : f (s x) = x := LinearMap.congr_fun hs x
    conv_rhs => rw [← h1, ← Finset.univ_sum_single (s x), map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← map_smul]
    congr 1
    ext j
    by_cases hij : j = i
    · subst hij; simp [c]
    · simp [c, Pi.single_eq_of_ne hij]
  let Ψ : ⋀[R]^2 V →ₗ[R] ⋀[R]^2 V :=
    ∑ i, ∑ j, if i < j then (LinearMap.toSpanSingleton R _ (b2 (e i) (e j))) ∘ₗ pair2 (c i) (c j) else 0
  have hΨ : Ψ = LinearMap.id := ext2 fun a b ↦ by
    let g : Fin n → Fin n → ⋀[R]^2 V := fun i j ↦ (c i a * c j b) • b2 (e i) (e j)
    have hg0 : ∀ i, g i i = 0 := fun i ↦ by simp [g, wedge_basis_self_zero]
    have h1 : i2 a b = ∑ i, ∑ j, g i j := by
      conv_lhs => rw [← wedge_basis_apply, ← he a, ← he b]
      simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, Finset.smul_sum, g, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      rw [mul_comm]
    have h2 : ∑ i, ∑ j, (if i < j then g j i else 0) = ∑ i, ∑ j, (if j < i then g i j else 0) :=
      Finset.sum_comm
    have h3 : Ψ (i2 a b) = ∑ i, ∑ j, ((if i < j then g i j else 0) + if i < j then g j i else 0) := by
      simp only [Ψ, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      split_ifs with hij
      · rw [LinearMap.comp_apply, exterior_pairing_iota_two, LinearMap.toSpanSingleton_apply]
        simp only [g]
        rw [wedge_basis_swap_neg (e i) (e j)]
        module
      · simp
    rw [h3, LinearMap.id_apply, h1]
    simp only [Finset.sum_add_distrib]
    rw [h2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [hij, hij.not_gt]
    · subst hij; simp [hg0]
    · simp [hij, hij.not_gt]
  have := LinearMap.congr_fun hΨ t
  rw [LinearMap.id_apply] at this
  rw [← this]
  simp only [Ψ, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun j _ ↦ ?_
  split_ifs <;> simp [h]
end GlobalTheory.CompanionTheory.Hodge.LiftO
