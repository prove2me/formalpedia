-- Prove2me | solution 1 for ModularCurve.exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_apply_eq_one_iff_of_charZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/ebeef6ea-7847-5595-926c-7b4bdffe5992

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_CohCarrier_Level
import Theorems.Thm_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero
import Theorems.Thm_ModularCurve_exists_intSeriesC_mul_ne_of_gamma0Units_not_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_apply_eq_one_iff_of_charZero
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open scoped MatrixGroups ModularForm

namespace T3FaithAssembly

open CongruenceSubgroup

theorem neg_mem_gamma0 {M : ℕ} {A : SL(2, ℤ)} (hA : A ∈ Gamma0 M) : -A ∈ Gamma0 M := by
  rw [Gamma0_mem] at hA ⊢
  rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, hA, neg_zero]

theorem neg_one_mem_gamma0 (M : ℕ) : (-1 : SL(2, ℤ)) ∈ Gamma0 M := neg_mem_gamma0 (one_mem _)

theorem gamma0Units_neg {M : ℕ} [NeZero M] {A : SL(2, ℤ)} (hA : A ∈ Gamma0 M) :
    CohCarrier.gamma0Units M ⟨-A, neg_mem_gamma0 hA⟩ = -CohCarrier.gamma0Units M ⟨A, hA⟩ := by
  ext
  rw [CohCarrier.val_gamma0Units, Units.val_neg, CohCarrier.val_gamma0Units]
  show (((-A : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = -(((A : SL(2, ℤ)) 1 1 : ℤ) : ZMod M)
  rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg]

theorem mem_or_neg_mem {M : ℕ} [NeZero M] (H : Subgroup (ZMod M)ˣ) (γ : Gamma0 M)
    (hd : CohCarrier.gamma0Units M γ ∈ H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)) :
    (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M H ∨ -(γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M H := by
  have h2 : (-1 : (ZMod M)ˣ) ^ (2 : ℤ) = 1 := by
    rw [zpow_two]; simp
  rw [Subgroup.mem_sup] at hd
  obtain ⟨h, hh, u, hu, hhu⟩ := hd
  rw [Subgroup.mem_zpowers_iff] at hu
  obtain ⟨k, rfl⟩ := hu
  rcases Int.even_or_odd k with ⟨l, rfl⟩ | ⟨l, rfl⟩
  · left
    refine CohCarrier.mem_GammaH_iff.mpr ⟨γ.2, ?_⟩
    have : (-1 : (ZMod M)ˣ) ^ (l + l) = 1 := by rw [← two_mul, zpow_mul, h2, one_zpow]
    rw [this, mul_one] at hhu
    rw [Subtype.coe_eta, ← hhu]
    exact hh
  · right
    refine CohCarrier.mem_GammaH_iff.mpr ⟨neg_mem_gamma0 γ.2, ?_⟩
    have : (-1 : (ZMod M)ˣ) ^ (2 * l + 1) = -1 := by
      rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]
    rw [this] at hhu
    rw [gamma0Units_neg γ.2, Subtype.coe_eta, ← hhu, mul_neg_one, neg_neg]
    exact hh

end T3FaithAssembly

open T3FaithAssembly in
theorem solution
    (K : Type*) [Field K] [CharZero K] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    ∃ ρ : CongruenceSubgroup.Gamma0 M →*
        (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H) ≃ₐ[K]
          ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)),
      (∀ (γ : CongruenceSubgroup.Gamma0 M) (x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)),
        (x : LaurentSeries K) ∈ ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M) →
          ρ γ x = x) ∧
      (∀ γ : CongruenceSubgroup.Gamma0 M,
        ρ γ = 1 ↔ CohCarrier.gamma0Units M γ ∈ H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)) := by
  classical
  obtain ⟨ρ, hH, hneg, hfix, hslash⟩ :=
    ModularCurve.exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero K M H
  refine ⟨ρ, hfix, fun γ => ⟨fun hρ => ?_, fun hd => ?_⟩⟩
  ·
    by_contra hd
    have hM : ((M : ℕ) : K) ≠ 0 := by exact_mod_cast (NeZero.ne M)
    obtain ⟨k, f, g, f₁, g₁, pf, pg, pf₁, pg₁, c, hc, hf, hg, hf₁, hg₁, hfs, hgs, hpg, hpg₁, hne⟩ :=
      ModularCurve.exists_intSeriesC_mul_ne_of_gamma0Units_not_mem K M hM H (γ : SL(2, ℤ)) γ.2
        (by rw [Subtype.coe_eta]; exact hd)
    have key := hslash γ f g f₁ g₁ c hc hf hg hf₁ hg₁ hfs hgs hpg hpg₁
    rw [hρ, AlgEquiv.one_apply] at key

    apply hne
    have key' : ModularCurve.intSeriesC K pf / ModularCurve.intSeriesC K pg =
        ModularCurve.intSeriesC K pf₁ / ModularCurve.intSeriesC K pg₁ := key
    rw [div_eq_div_iff hpg hpg₁] at key'
    rw [key', mul_comm]
  ·
    rcases mem_or_neg_mem H γ hd with hγ | hγ
    · exact hH γ hγ
    · have hdecomp : γ = ⟨-1, neg_one_mem_gamma0 M⟩ * ⟨-(γ : SL(2, ℤ)), neg_mem_gamma0 γ.2⟩ := by
        apply Subtype.ext
        show (γ : SL(2, ℤ)) = -1 * -(γ : SL(2, ℤ))
        rw [neg_one_mul, neg_neg]
      rw [hdecomp, map_mul, hneg ⟨-1, neg_one_mem_gamma0 M⟩ rfl, hH ⟨-(γ : SL(2, ℤ)), neg_mem_gamma0 γ.2⟩ hγ,
        mul_one]

end S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_apply_eq_one_iff_of_charZero
end P2MW
export P2MW.S_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_apply_eq_one_iff_of_charZero (solution)
