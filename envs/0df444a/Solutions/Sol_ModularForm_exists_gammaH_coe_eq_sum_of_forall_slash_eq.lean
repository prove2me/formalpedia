-- Prove2me | solution 1 for ModularForm.exists_gammaH_coe_eq_sum_of_forall_slash_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/577595de-867d-56ad-b672-9050937c4daf

import Mathlib
import Definitions.Def_CohCarrier_Level
import Theorems.Thm_ModularForm_exists_gammaH_coe_eq_of_forall_slash_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_exists_gammaH_coe_eq_sum_of_forall_slash_eq

set_option autoImplicit false

open scoped MatrixGroups ModularForm

private theorem sum_slash {ι : Type*} (s : Finset ι) (k : ℤ) (γ : GL (Fin 2) ℝ)
    (f : ι → UpperHalfPlane → ℂ) :
    (∑ i ∈ s, f i) ∣[k] γ = ∑ i ∈ s, f i ∣[k] γ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [SlashAction.zero_slash]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih]

theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) [Fintype H] (k : ℤ)
    (F : ZMod M → ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
    (hF : ∀ (t : ZMod M) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M →
      (⇑(F t) : UpperHalfPlane → ℂ) ∣[k] γ = ⇑(F (t * ((γ 1 1 : ℤ) : ZMod M)))) :
    ∃ V : ZMod M → ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k,
      (∀ t : ZMod M, (⇑(V t) : UpperHalfPlane → ℂ) =
        ∑ h : H, (⇑(F (t * ((h : (ZMod M)ˣ) : ZMod M))) : UpperHalfPlane → ℂ)) ∧
      (∀ (t : ZMod M) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M →
        (⇑(V t) : UpperHalfPlane → ℂ) ∣[k] γ = ⇑(V (t * ((γ 1 1 : ℤ) : ZMod M)))) := by
  classical

  let G : ZMod M → ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k :=
    fun t => ∑ h : H, F (t * ((h : (ZMod M)ˣ) : ZMod M))
  have hGcoe : ∀ t, (⇑(G t) : UpperHalfPlane → ℂ) =
      ∑ h : H, (⇑(F (t * ((h : (ZMod M)ˣ) : ZMod M))) : UpperHalfPlane → ℂ) := by
    intro t
    show FunLike.coeAddMonoidHom _ UpperHalfPlane ℂ (G t) = _
    simp only [G, map_sum]
    rfl

  have hGslash : ∀ (t : ZMod M) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M →
      (⇑(G t) : UpperHalfPlane → ℂ) ∣[k] γ = ⇑(G (t * ((γ 1 1 : ℤ) : ZMod M))) := by
    intro t γ hγ
    rw [hGcoe, hGcoe, ModularForm.SL_slash, sum_slash]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [← ModularForm.SL_slash, hF _ γ hγ, mul_right_comm]

  have hGH : ∀ (t : ZMod M) (u : (ZMod M)ˣ), u ∈ H → G (t * (u : ZMod M)) = G t := by
    intro t u hu
    simp only [G]
    exact Fintype.sum_equiv (Equiv.mulLeft (⟨u, hu⟩ : H)) _ _ (fun h => by
      simp [mul_assoc])

  have hGinv : ∀ t, ∀ γ ∈ CohCarrier.GammaH M H, (⇑(G t) : UpperHalfPlane → ℂ) ∣[k] γ = ⇑(G t) := by
    intro t γ hγ
    obtain ⟨h0, hH⟩ := CohCarrier.mem_GammaH_iff.mp hγ
    rw [hGslash t γ h0]
    have := hGH t _ hH
    rw [CohCarrier.val_gamma0Units] at this
    exact congrArg _ this
  choose V hV using fun t =>
    ModularForm.exists_gammaH_coe_eq_of_forall_slash_eq M H k (G t) (hGinv t)
  refine ⟨V, fun t => (hV t).trans (hGcoe t), fun t γ hγ => ?_⟩
  rw [hV, hV, hGslash t γ hγ]

end S_ModularForm_exists_gammaH_coe_eq_sum_of_forall_slash_eq
end P2MW
export P2MW.S_ModularForm_exists_gammaH_coe_eq_sum_of_forall_slash_eq (solution)
