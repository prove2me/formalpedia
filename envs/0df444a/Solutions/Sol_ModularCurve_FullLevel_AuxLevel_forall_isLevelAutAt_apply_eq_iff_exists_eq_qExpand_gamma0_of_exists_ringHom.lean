-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevel.forall_isLevelAutAt_apply_eq_iff_exists_eq_qExpand_gamma0_of_exists_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/aebb4c2b-3c96-5e7f-8658-9c52372be6a7

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Theorems.Thm_ModularCurve_FullLevel_qExpand_mem_and_apply_eq_of_isLevelAutAt_of_mem_Gamma_of_exists_ringHom
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_forall_isLevelAutAt_apply_eq_iff_exists_eq_qExpand_of_exists_ringHom
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom
import Theorems.Thm_ModularCurve_FullLevel_exists_isLevelAutAt_of_mem_gamma0
import Theorems.Thm_ModularCurve_FullLevel_forall_isLevelAutAt_apply_eq_iff_exists_eq_qExpand
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_coe_apply_eq_qExpand_coe_apply_of_isLevelAutAt_of_exists_ringHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_forall_isLevelAutAt_apply_eq_iff_exists_eq_qExpand_gamma0_of_exists_ringHom
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open scoped MatrixGroups

namespace FFG0Reduce

theorem levelH_one_eq_top (M' : ℕ) : ModularCurve.FullLevel.levelH 1 M' = ⊤ := by
  haveI : Subsingleton (ZMod 1) := ZMod.subsingleton_iff.mpr rfl
  rw [eq_top_iff]
  intro u _
  rw [ModularCurve.FullLevel.mem_levelH_iff]
  exact Units.ext (Subsingleton.elim _ _)

theorem xHFunctionField_levelH_one (M' : ℕ) :
    ModularCurve.xHFunctionField (1 ^ 2 * M') (ModularCurve.FullLevel.levelH 1 M') =
      ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M') := by
  rw [levelH_one_eq_top]
  show ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (1 ^ 2 * M') ⊤) = _
  rw [CohCarrier.GammaH_top, one_pow, one_mul]

theorem isLevelAutAt_congr_level (L : Type) [Field L] [CharZero L] (ζ : L) (M' : ℕ) {m m' : ℕ} [NeZero m] [NeZero m']
    (h : m = m') (γ : SL(2, ℤ)) (K : IntermediateField L (LaurentSeries L)) (τ : ↥K ≃ₐ[L] ↥K) :
    ModularCurve.FullLevel.IsLevelAutAt L m ζ m (m ^ 2 * M') (ModularCurve.FullLevel.levelH m M') γ K τ ↔
      ModularCurve.FullLevel.IsLevelAutAt L m' ζ m' (m' ^ 2 * M') (ModularCurve.FullLevel.levelH m' M') γ K τ := by
  subst h
  exact Iff.rfl

end FFG0Reduce

open FFG0Reduce

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M'))) :
    (∀ x : LaurentSeries L,
      x ∈ ModularCurve.laurentBaseChange L
            (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')) →
        ModularCurve.qExpand L (q * ℓ) x ∈ K) ∧
    (∀ w : ↥K,
      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            τ w = w) ↔
        ∃ x : LaurentSeries L,
          x ∈ ModularCurve.laurentBaseChange L
            (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')) ∧
          ((w : ↥K) : LaurentSeries L) = ModularCurve.qExpand L (q * ℓ) x) := by
  classical

  have e1 : (1 : ℕ) * (q * ℓ) = q * ℓ := one_mul _
  have hξ1 : IsPrimitiveRoot ξ (1 * (q * ℓ)) := by rw [e1]; exact hξ
  have hK1 : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((1 * (q * ℓ)) ^ 2 * M') (ModularCurve.FullLevel.levelH (1 * (q * ℓ)) M')) := by
    rw [e1]; exact hK
  have hι1 : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (((1 : ℕ) : ℂ) * ((q * ℓ : ℕ) : ℂ))) := by
    obtain ⟨ι, hι⟩ := hιξ
    refine ⟨ι, ?_⟩
    rw [hι]
    congr 1
    push_cast
    ring
  obtain ⟨h0i, h0ii⟩ := ModularCurve.FullLevel.qExpand_mem_and_apply_eq_of_isLevelAutAt_of_mem_Gamma_of_exists_ringHom 1 M' (Nat.coprime_one_left M') (q * ℓ) L ξ hξ1 hι1 K hK1
  have hsrc : ModularCurve.laurentBaseChange L
        (ModularCurve.xHFunctionField (1 ^ 2 * M') (ModularCurve.FullLevel.levelH 1 M')) =
      ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')) := by
    rw [xHFunctionField_levelH_one]
  refine ⟨?_, ?_⟩
  ·
    intro x hx
    have hx' : x ∈ ModularCurve.laurentBaseChange L
        (ModularCurve.xHFunctionField (1 ^ 2 * M') (ModularCurve.FullLevel.levelH 1 M')) := by rw [hsrc]; exact hx
    exact h0i x hx'
  · intro w
    constructor
    ·
      intro hfix
      obtain ⟨-, h746⟩ := ModularCurve.FullLevel.AuxLevel.forall_isLevelAutAt_apply_eq_iff_exists_eq_qExpand_of_exists_ringHom q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hιξ K hK
      obtain ⟨x₁, hx₁, hwx₁⟩ := (h746 w).mp (fun γ _ hγ0 τ hτ => hfix γ hγ0 τ hτ)
      set Kq : IntermediateField L (LaurentSeries L) := ModularCurve.laurentBaseChange L
        (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) with hKq
      have hqpos : 0 < q * ℓ := Nat.pos_of_ne_zero (NeZero.ne _)
      have hζ : IsPrimitiveRoot (ξ ^ ℓ) q := hξ.pow hqpos (mul_comm q ℓ)
      have hex := ModularCurve.FullLevel.exists_isLevelAutAt_of_mem_gamma0 q hq M' hqM' L (ξ ^ ℓ) hζ Kq hKq
      let τq : SL(2, ℤ) → (↥Kq ≃ₐ[L] ↥Kq) := fun γ =>
        if h : γ ∈ CongruenceSubgroup.Gamma0 M' then (hex γ h).choose else AlgEquiv.refl
      have hτq : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ModularCurve.FullLevel.IsLevelAutAt L q (ξ ^ ℓ) q (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') γ⁻¹ Kq (τq γ) := by
        intro γ h
        simp only [τq, dif_pos h]
        exact (hex γ h).choose_spec
      let x₁' : ↥Kq := ⟨x₁, hx₁⟩
      have hfixq : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → τq γ x₁' = x₁' := by
        intro γ hγ
        obtain ⟨τ, hτ⟩ := ModularCurve.FullLevel.AuxLevel.exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hιξ K hK γ hγ
        have h1 := ModularCurve.FullLevel.AuxLevel.coe_apply_eq_qExpand_coe_apply_of_isLevelAutAt_of_exists_ringHom q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hιξ K hK Kq hKq γ hγ τ hτ (τq γ) (hτq γ hγ) x₁' w hwx₁
        rw [hfix γ hγ τ hτ, hwx₁] at h1
        exact (Subtype.ext (ModularCurve.qExpand_injective ℓ h1)).symm
      obtain ⟨ι, hι⟩ := hιξ
      have hιq : ∃ ι : L →+* ℂ, ι (ξ ^ ℓ) = Complex.exp (2 * Real.pi * Complex.I / q) := by
        refine ⟨ι, ?_⟩
        rw [map_pow, hι, ← Complex.exp_nat_mul]
        congr 1
        have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
        have hℓ0 : (ℓ : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne ℓ)
        push_cast
        field_simp
      obtain ⟨g, hg, hxg⟩ :=
        (ModularCurve.FullLevel.forall_isLevelAutAt_apply_eq_iff_exists_eq_qExpand q hq M' hqM' L (ξ ^ ℓ) hζ hιq Kq hKq τq hτq x₁').mp hfixq
      refine ⟨g, hg, ?_⟩
      have hx₁c : (x₁ : LaurentSeries L) = ((x₁' : ↥Kq) : LaurentSeries L) := rfl
      rw [hwx₁, hx₁c, hxg, ModularCurve.qExpand_qExpand, ModularCurve.qExpand_congr (mul_comm ℓ q)]
    ·
      rintro ⟨g, hg, hwg⟩ γ hγ τ hτ
      have hg' : g ∈ ModularCurve.laurentBaseChange L
          (ModularCurve.xHFunctionField (1 ^ 2 * M') (ModularCurve.FullLevel.levelH 1 M')) := by rw [hsrc]; exact hg
      have hτ' := (isLevelAutAt_congr_level L ξ M' e1 γ⁻¹ K τ).mpr hτ
      exact h0ii g hg' w hwg γ (by rw [CongruenceSubgroup.Gamma_one_top]; exact Subgroup.mem_top γ) hγ τ hτ'

end S_ModularCurve_FullLevel_AuxLevel_forall_isLevelAutAt_apply_eq_iff_exists_eq_qExpand_gamma0_of_exists_ringHom
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevel_forall_isLevelAutAt_apply_eq_iff_exists_eq_qExpand_gamma0_of_exists_ringHom (solution)
