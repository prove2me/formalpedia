-- Prove2me | solution 1 for GroundTheory.ProfCoh.g_integerUnits_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:45:21.382805+00:00
-- url     : https://prove2.me/submissions/80da4c4f-91df-4b3e-8cf7-2c3107d883c7

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsLattice
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep
import Theorems.Thm_GroundTheory_ProfCoh_modNEquivOfSurjective_apply_modNRep
import Theorems.Thm_GroundTheory_ProfCoh_finite_quotient_range_toAdditive
import Theorems.Thm_GroundTheory_ProfCoh_toAdditive_subtype_injective
import Theorems.Thm_GroundTheory_ProfCoh_finite_modN_of_finite_cokernel
import Theorems.Thm_GroundTheory_ProfCoh_finite_torsN_of_torsion_trivial
import Theorems.Thm_GroundTheory_ProfCoh_integer_subgroup_torsion
import Theorems.Thm_GroundTheory_ProfCoh_finrank_modN_integer
import Theorems.Thm_GroundTheory_ProfCoh_finite_modN_maxPow
import Theorems.Thm_GroundTheory_ProfCoh_exists_maxPow_le_normalSub
import Theorems.Thm_GroundTheory_ProfCoh_finite_quotient_maxPow
import Theorems.Thm_GroundTheory_LocalField_coe_smul_integerUnits
import Theorems.Thm_GroundTheory_LocalField_exists_normalBasis_integer
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_g_eq_of_finite_cokernel
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_g_eq_of_torsion_trivial
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_toFun_congr
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_toFun_pi
import Theorems.Thm_GroundTheory_ProfCoh_coe_torsNRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_coeffToRegular_eq_zero_iff
import Theorems.Thm_GroundTheory_ProfCoh_coeffToRegular_perm
import Theorems.Thm_GroundTheory_ProfCoh_coeffToRegular_surjective
import Theorems.Thm_GroundTheory_ProfCoh_eq_one_of_mem_unitFiltration_of_pow_eq_one
import Theorems.Thm_GroundTheory_ProfCoh_modNRep_mk
import Theorems.Thm_GroundTheory_ProfCoh_normalSubEquiv_apply
import Theorems.Thm_GroundTheory_ProfCoh_smul_normalSubOfCoeff
import Theorems.Thm_GroundTheory_ProfCoh_unitToModN_eq_zero_iff
import Theorems.Thm_GroundTheory_ProfCoh_unitToModN_smul
import Theorems.Thm_GroundTheory_ProfCoh_unitToModN_surjective
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_AdicCompleteRootExistence_exists_root_of_dvd__8130b8fccf10
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_smul_integerUnits
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply
attribute [local simp] GroundTheory.ProfCoh.coe_torsNRep_apply
attribute [local simp] GroundTheory.ProfCoh.modNRep_mk



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
universe u
open GroundTheory.LocalField ValuativeRel IsLocalRing
variable {E F : Type u} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra E F] [ValuativeExtension E F] [FiniteDimensional E F] [IsGalois E F]
  {l : ℕ} [Fact l.Prime] (d : AdditiveFunction.{u} l (F ≃ₐ[E] F))
attribute [local instance] integerAction unitFiltrationAction maxPowAction normalSubAction
namespace GroundTheory.ProfCoh
theorem _root_.solution (hl : (l : F) ≠ 0) {n : ℕ}
    (hn : Nat.card (𝒪[E] ⧸ Ideal.span {(l : 𝒪[E])}) = l ^ n) :
    Finite (ModN (Additive 𝒪[F]ˣ) l) ∧
      d.g (Additive 𝒪[F]ˣ) = n * d.toFun (MonoidAlgebra (ZMod l) (F ≃ₐ[E] F))
        (Representation.leftRegular (ZMod l) (F ≃ₐ[E] F)) := by
  have hlp : l.Prime := Fact.out
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hl' : (l : 𝒪[F]) ≠ 0 := fun h ↦ hl (by simpa using congrArg Subtype.val h)
  obtain ⟨e, ε, hpe⟩ : ∃ (e : ℕ) (ε : 𝒪[F]ˣ), (l : 𝒪[F]) = ϖ ^ e * ε := by
    obtain ⟨e, ε, h⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl' hϖ
    exact ⟨e, ε, by rw [h, mul_comm]⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[E]
  obtain ⟨θ, hθ, hθO⟩ := exists_normalBasis_integer (K := E) (L := F) hπ
  obtain ⟨j, hj⟩ := exists_maxPow_le_normalSub hθ
  have hk : e + 1 ≤ max j (e + 1) := le_max_right _ _
  have hle : maxPow F (max j (e + 1)) ≤ normalSub E θ := hj _ (le_max_left _ _)
  set k := max j (e + 1)
  obtain ⟨hfinE, hrank⟩ := finrank_modN_integer (E := E) hn
  let b : Module.Basis (Fin n) (ZMod l) (ModN 𝒪[E] l) := Module.finBasisOfFinrankEq _ _ hrank

  set U := unitFiltration F k
  have hUt : ∀ a : Additive U, l • a = 0 → a = 0 := by
    intro a ha
    apply Additive.toMul.injective
    have h1 : (a.toMul : 𝒪[F]ˣ) ^ l = 1 := by
      have := congrArg (fun b : Additive U ↦ ((b.toMul : U) : 𝒪[F]ˣ)) ha
      simpa using this
    exact Subtype.ext (eq_one_of_mem_unitFiltration_of_pow_eq_one hϖ hlp hpe hk a.toMul.2 h1)
  let e1 := modNEquivOfSurjective (unitToModN hϖ hpe (Nat.le_of_succ_le hk))
    (unitToModN_surjective hϖ hpe hk) (unitToModN_eq_zero_iff hϖ hpe hlp hk)
  have he1 := modNEquivOfSurjective_apply_modNRep (modNRep (F ≃ₐ[E] F) (maxPow F k) l)
    (unitToModN hϖ hpe (Nat.le_of_succ_le hk)) (unitToModN_surjective hϖ hpe hk)
    (unitToModN_eq_zero_iff hϖ hpe hlp hk) (unitToModN_smul ϖ hϖ hpe _)
  have := finite_modN_maxPow hϖ hpe k
  have : Finite (ModN (Additive U) l) := Finite.of_equiv _ e1.symm.toEquiv
  have := finite_torsN_of_torsion_trivial hUt
  have hPt : ∀ a : maxPow F k, l • a = 0 → a = 0 := integer_subgroup_torsion hl _
  have := finite_torsN_of_torsion_trivial hPt

  let N := normalSubEquiv hθ hθO
  let φ : normalSub E θ →+ (Fin n → MonoidAlgebra (ZMod l) (F ≃ₐ[E] F)) :=
    (coeffToRegular b).comp N.symm.toAddMonoidHom
  have hφs : Function.Surjective φ :=
    (coeffToRegular_surjective (F ≃ₐ[E] F) b).comp N.symm.surjective
  have hφk : ∀ t, φ t = 0 ↔ t ∈ LinearMap.range (LinearMap.lsmul ℤ (normalSub E θ) l) := by
    intro t
    change coeffToRegular b (N.symm t) = 0 ↔ _
    rw [coeffToRegular_eq_zero_iff, mem_range_lsmul_iff, mem_range_lsmul_iff]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨N y, by rw [← map_nsmul, hy, AddEquiv.apply_symm_apply]⟩
    · rintro ⟨y, rfl⟩
      exact ⟨N.symm y, by rw [map_nsmul]⟩
  have hφγ : ∀ (σ : F ≃ₐ[E] F) (t : normalSub E θ), φ (σ • t) =
      piRep (Fin n) (Representation.leftRegular (ZMod l) (F ≃ₐ[E] F)) σ (φ t) := by
    intro σ t
    obtain ⟨c, rfl⟩ := N.surjective t
    change coeffToRegular b (N.symm (σ • N c)) = piRep (Fin n)
      (Representation.leftRegular (ZMod l) (F ≃ₐ[E] F)) σ (coeffToRegular b (N.symm (N c)))
    rw [AddEquiv.symm_apply_apply, normalSubEquiv_apply, smul_normalSubOfCoeff,
      ← normalSubEquiv_apply hθ, AddEquiv.symm_apply_apply, coeffToRegular_perm]
  let e2 := modNEquivOfSurjective φ hφs hφk
  have he2 := modNEquivOfSurjective_apply_modNRep _ φ hφs hφk hφγ
  have : Finite (ModN (normalSub E θ) l) := Finite.of_equiv _ e2.symm.toEquiv
  have hTt : ∀ a : normalSub E θ, l • a = 0 → a = 0 := integer_subgroup_torsion hl _
  have := finite_quotient_maxPow hle
  have := finite_quotient_range_toAdditive U
  refine ⟨finite_modN_of_finite_cokernel U.subtype.toAdditive, ?_⟩
  rw [d.g_eq_of_finite_cokernel U.subtype.toAdditive (fun _ _ ↦ rfl)
      (toAdditive_subtype_injective U),
    d.g_eq_of_torsion_trivial (Additive U) hUt, d.toFun_congr _ _ e1 he1,
    ← d.g_eq_of_torsion_trivial (maxPow F k) hPt,
    ← d.g_eq_of_finite_cokernel (AddSubgroup.inclusion hle) (fun _ _ ↦ rfl)
      (AddSubgroup.inclusion_injective hle),
    d.g_eq_of_torsion_trivial (normalSub E θ) hTt, d.toFun_congr _ _ e2 he2, d.toFun_pi]
end GroundTheory.ProfCoh
