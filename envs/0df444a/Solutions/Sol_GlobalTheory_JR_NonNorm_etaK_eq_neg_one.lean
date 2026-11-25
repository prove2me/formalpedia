-- Prove2me | solution 1 for GlobalTheory.JR.NonNorm.etaK_eq_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:12:12.125769+00:00
-- url     : https://prove2.me/submissions/98bdb24d-f196-4d54-b6d4-6de00fea8a66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSplitting
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedNormSurj
import Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaKEqNegOneOfNotNorm
import Theorems.Thm_GlobalTheory_JR_NonNorm_not_two_dvd_ord_norm
import Theorems.Thm_GlobalTheory_JR_NonNorm_ord_eq_of_norm_eq
import Theorems.Thm_GlobalTheory_JR_Et_quadratic_structure
import Theorems.Thm_GroundTheory_LocalField_IsUnramified_residueDegree_eq_finrank
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_galoisEquivResidue_apply
import Theorems.Thm_GroundTheory_LocalField_ord_algebraMap
import Theorems.Thm_GroundTheory_LocalField_ord_pow
import Theorems.Thm_GroundTheory_LocalField_ord_uniformizer
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_residueDegree_eq_finrank
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.galoisEquivResidue_apply
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.NonNorm
open ValuativeRel GroundTheory.LocalField IntermediateField
namespace GlobalTheory.JR.NonNorm
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsField A.K → IsField A.L → ∀ s : A.Kˣ, (¬ ∃ y : A.L, A.NL y = s) → A.etaK s = -1 := by
  intro F E _ _ _ _ hU A hK hL s hs
  haveI := hU.ultraF
  haveI := hU.ultraE
  haveI := hU.lcF
  haveI := hU.lcE
  letI := normRel F
  letI := normRel E
  haveI := isLocalField F
  haveI := isLocalField E
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  haveI : ValuativeExtension F E := ⟨fun a b => by
    change ‖algebraMap F E a‖ ≤ ‖algebraMap F E b‖ ↔ ‖a‖ ≤ ‖b‖
    rw [norm_algebraMap', norm_algebraMap']⟩
  have he : ramificationIndex F E = 1 := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[E]
    obtain ⟨x, hx⟩ := hU.unram (π : E)
    have h1 := ord_eq_of_norm_eq E (π : E) (algebraMap F E x) (by rw [norm_algebraMap', hx])
    rw [ord_uniformizer hπ, ord_algebraMap] at h1
    have h2 : (ramificationIndex F E : ℤ) ∣ 1 := ⟨_, h1⟩
    exact Nat.dvd_one.1 (by exact_mod_cast h2)
  obtain ⟨ζ, hζ, htop⟩ := exists_isPrimitiveRoot_adjoin_eq_top_of_unramified F E he
  have hcard : Nat.card 𝓀[E] = Nat.card 𝓀[F] ^ 2 := by
    rw [← hU.finrank_eq, ← residueDegree_eq_finrank_of_unramified F E he, residueDegree_eq_finrank]
    exact Module.natCard_eq_pow_finrank
  rw [hcard] at hζ
  obtain ⟨⟨b⟩, -⟩ := Et.quadratic_structure F E A
  letI : Field A.K := hK.toField
  letI : Field A.L := hL.toField
  have h2 : Module.finrank A.K A.L = 2 := by simpa using Module.finrank_eq_card_basis b
  have hζ' : IsPrimitiveRoot (algebraMap E A.L ζ) (Nat.card 𝓀[F] ^ 2 - 1) :=
    hζ.map_of_injective (algebraMap E A.L).injective
  have hE : ∀ e : E, algebraMap E A.L e ∈ A.K⟮algebraMap E A.L ζ⟯ := by
    intro e
    have he' : e ∈ F⟮ζ⟯ := by rw [htop]; trivial
    induction he' using IntermediateField.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff.1 hx]
      exact mem_adjoin_simple_self _ _
    | algebraMap x =>
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply F A.K A.L]
      exact IntermediateField.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have htop' : A.K⟮algebraMap E A.L ζ⟯ = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hbc := A.push.symm.out
    induction y using hbc.inductionOn with
    | zero => exact zero_mem _
    | tmul e => exact hE e
    | smul k y hy => exact IntermediateField.smul_mem _ (hy trivial)
    | add y z hy hz => exact add_mem (hy trivial) (hz trivial)
  have hodd := not_two_dvd_ord_norm F A.K A.L h2 _ hζ' htop' s s.ne_zero hs
  unfold Et.etaK eta
  rw [if_neg]
  rintro ⟨y, hy⟩
  apply hodd
  have hy0 : y ≠ 0 := by
    rintro rfl
    have h0 : Algebra.norm F (s : A.K) = 0 := norm_eq_zero.1 (by simpa using hy)
    exact s.ne_zero (Algebra.norm_eq_zero_iff.1 h0)
  have h3 := ord_eq_of_norm_eq F (Algebra.norm F (s : A.K)) (y ^ 2) (by rw [norm_pow, hy])
  rw [ord_pow hy0] at h3
  exact ⟨ord y, by exact_mod_cast h3⟩
end GlobalTheory.JR.NonNorm
