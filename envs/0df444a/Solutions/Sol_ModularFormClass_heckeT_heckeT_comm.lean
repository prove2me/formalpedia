-- Prove2me | solution 1 for ModularFormClass.heckeT_heckeT_comm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/ac188186-6cc5-544c-826e-641d46eb8f9b

import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_UpperHalfPlane_qCoeff_heckeT
import Theorems.Thm_ModularForm_mdifferentiable_heckeT
import Theorems.Thm_ModularForm_isBoundedAtImInfty_heckeT
import Theorems.Thm_ModularForm_periodic_heckeT_comp_ofComplex
import Theorems.Thm_UpperHalfPlane_eq_of_forall_qCoeff_eq
import Theorems.Thm_ModularForm_coeffHeckeT_comm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularFormClass_heckeT_heckeT_comm

set_option autoImplicit false

noncomputable section

open Complex Function Filter
p2m_open "UpperHalfPlane~I"
open scoped Real MatrixGroups ModularForm Manifold Topology

open ModularForm ModularFormClass

namespace W2WsF

private theorem _root_.W2WsF.eq_of_forall_qCoeff_eq {f g : ℍ → ℂ} (hfper : Periodic (f ∘ ofComplex) 1) (hfhol : MDiff f)
    (hfbdd : IsBoundedAtImInfty f) (hgper : Periodic (g ∘ ofComplex) 1) (hghol : MDiff g)
    (hgbdd : IsBoundedAtImInfty g) (h : ∀ n : ℕ, qCoeff f n = qCoeff g n) : f = g :=
  UpperHalfPlane.eq_of_forall_qCoeff_eq hfper hfhol hfbdd hgper hghol hgbdd h

p2m_export "W2WsF" "eq_of_forall_qCoeff_eq"

theorem qCoeff_const_smul {f : ℍ → ℂ} (hper : Periodic (f ∘ ofComplex) 1) (hhol : MDiff f)
    (hbdd : IsBoundedAtImInfty f) (c : ℂ) (n : ℕ) : qCoeff (c • f) n = c * qCoeff f n := by
  simp only [qCoeff]
  rw [UpperHalfPlane.qExpansion_smul (analyticAt_cuspFunction_zero one_pos hper hhol hbdd)]
  simp

theorem periodic_const_smul {f : ℍ → ℂ} (hper : Periodic (f ∘ ofComplex) 1) (c : ℂ) :
    Periodic ((c • f) ∘ ofComplex) 1 := fun z ↦ by
  simpa using congrArg (c * ·) (hper z)

section Class

variable {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

theorem mf_periodic [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) :
    Periodic (⇑f ∘ ofComplex) 1 :=
  SlashInvariantFormClass.periodic_comp_ofComplex f hΓ

theorem mf_bdd [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) :
    IsBoundedAtImInfty ⇑f :=
  haveI : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  bdd_at_infty f

end Class

theorem heckeT_heckeT_comm_bare {f : ℍ → ℂ} (hper : Periodic (f ∘ ofComplex) 1) (hhol : MDiff f)
    (hbdd : IsBoundedAtImInfty f) (k : ℤ) {p q : ℕ} (hpq : p.Coprime q) :
    heckeT k p (heckeT k q f) = heckeT k q (heckeT k p f) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  refine eq_of_forall_qCoeff_eq
    (periodic_heckeT_comp_ofComplex (periodic_heckeT_comp_ofComplex hper k q) k p)
    (mdifferentiable_heckeT (mdifferentiable_heckeT hhol k q) k p)
    (isBoundedAtImInfty_heckeT (isBoundedAtImInfty_heckeT hbdd k q) k p)
    (periodic_heckeT_comp_ofComplex (periodic_heckeT_comp_ofComplex hper k p) k q)
    (mdifferentiable_heckeT (mdifferentiable_heckeT hhol k p) k q)
    (isBoundedAtImInfty_heckeT (isBoundedAtImInfty_heckeT hbdd k p) k q) fun n ↦ ?_
  rw [UpperHalfPlane.qCoeff_heckeT (periodic_heckeT_comp_ofComplex hper k q)
      (mdifferentiable_heckeT hhol k q) (isBoundedAtImInfty_heckeT hbdd k q) k hp,
    UpperHalfPlane.qCoeff_heckeT (periodic_heckeT_comp_ofComplex hper k p)
      (mdifferentiable_heckeT hhol k p) (isBoundedAtImInfty_heckeT hbdd k p) k hq]
  have hq' : qCoeff (heckeT k q f) = coeffHeckeT k q (qCoeff f) :=
    funext fun m ↦ UpperHalfPlane.qCoeff_heckeT hper hhol hbdd k hq m
  have hp' : qCoeff (heckeT k p f) = coeffHeckeT k p (qCoeff f) :=
    funext fun m ↦ UpperHalfPlane.qCoeff_heckeT hper hhol hbdd k hp m
  rw [hq', hp', coeffHeckeT_comm k hpq]

end W2WsF

theorem solution {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {p q : ℕ} (hpq : Nat.Coprime p q) : ModularForm.heckeT k p (ModularForm.heckeT k q ⇑f) = ModularForm.heckeT k q (ModularForm.heckeT k p ⇑f) :=
  W2WsF.heckeT_heckeT_comm_bare (W2WsF.mf_periodic f hΓ) (ModularFormClass.holo f)
    (W2WsF.mf_bdd f hΓ) k hpq

end

end S_ModularFormClass_heckeT_heckeT_comm
end P2MW
export P2MW.S_ModularFormClass_heckeT_heckeT_comm (solution)
