-- Prove2me | solution 1 for ModularForm.exists_gammaH_coe_eq_of_forall_slash_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/28d5710b-3e92-5615-94a7-f52402bb051d

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_exists_gammaH_coe_eq_of_forall_slash_eq

set_option autoImplicit false

p2m_open_scoped "MatrixGroups ModularForm P2MW.S_ModularForm_exists_gammaH_coe_eq_of_forall_slash_eq.ModularForm"

private theorem Gamma_le_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) :
    CongruenceSubgroup.Gamma M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [CohCarrier.mem_GammaH_iff]
  have hA' := CongruenceSubgroup.Gamma_mem.mp hA
  have h0 : A ∈ CongruenceSubgroup.Gamma0 M := by
    rw [CongruenceSubgroup.Gamma0_mem]; exact hA'.2.2.1
  refine ⟨h0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, h0⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units]
    show ((A 1 1 : ℤ) : ZMod M) = ((1 : (ZMod M)ˣ) : ZMod M)
    rw [hA'.2.2.2, Units.val_one]
  rw [this]
  exact one_mem H

namespace ModularForm p2m_export "ModularForm" "holo' SL_slash ext bdd_at_cusps'" end ModularForm
p2m_open_scoped "ModularForm" in

private theorem ModularForm.exists_coe_eq_of_forall_slash_eq_of_finiteIndex
    (Γ Γ' : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] [Γ'.FiniteIndex] (k : ℤ)
    (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (hg : ∀ γ ∈ Γ', (⇑g : UpperHalfPlane → ℂ) ∣[k] γ = ⇑g) :
    ∃ f : ModularForm (Γ' : Subgroup (GL (Fin 2) ℝ)) k, (⇑f : UpperHalfPlane → ℂ) = ⇑g := by
  have hinv : ∀ γ ∈ ((Γ' : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)),
      (⇑g : UpperHalfPlane → ℂ) ∣[k] γ = ⇑g := by
    intro γ hγ
    obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hγ
    have h := hg A hA
    rw [ModularForm.SL_slash] at h
    exact h
  refine ⟨{ toFun := ⇑g
            slash_action_eq' := hinv
            holo' := g.holo'
            bdd_at_cusps' := fun {c} hc => ModularFormClass.bdd_at_cusps g
              ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mpr
                ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc)) }, rfl⟩

theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ)
    (g : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
    (hg : ∀ γ ∈ CohCarrier.GammaH M H, (⇑g : UpperHalfPlane → ℂ) ∣[k] γ = ⇑g) :
    ∃ f : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k,
      (⇑f : UpperHalfPlane → ℂ) = ⇑g := by
  haveI : (CohCarrier.GammaH M H).FiniteIndex := Subgroup.finiteIndex_of_le (Gamma_le_GammaH M H)
  exact ModularForm.exists_coe_eq_of_forall_slash_eq_of_finiteIndex _ _ k g hg

end S_ModularForm_exists_gammaH_coe_eq_of_forall_slash_eq
end P2MW
export P2MW.S_ModularForm_exists_gammaH_coe_eq_of_forall_slash_eq (solution)
