-- Prove2me | solution 1 for GlobalTheory.SigmaExtCount.card_stable_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:02:41.605439+00:00
-- url     : https://prove2.me/submissions/55053201-2af7-4c6e-b94e-e3459d1c60fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardSigmaStableProdLatticeExtSq
import Theorems.Thm_GlobalTheory_SigmaExtCount_gstab_iff
import Theorems.Thm_GlobalTheory_SigmaExtCount_twist_smul
import Theorems.Thm_GlobalTheory_SigmaExtCount_twist_twist
import Theorems.Thm_GlobalTheory_SigmaExtCount_twist_mem
import Theorems.Thm_GlobalTheory_SigmaExtCount_sstab_iff
import Theorems.Thm_GlobalTheory_SigmaExtCount_conj_inv_eq_neg

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
open GlobalTheory GlobalTheory.SigmaExtCount
variable {O : Type} [CommRing O] {cO : O →+* O} {A₁ A₂ : Type} [AddCommGroup A₁] [Module O A₁]
  [AddCommGroup A₂] [Module O A₂] {M₁ : Submodule O A₁} {M₂ : Submodule O A₂}
namespace GlobalTheory.SigmaExtCount
theorem _root_.solution (hcc : ∀ o, cO (cO o) = o) (θ : O) (hδ : IsUnit (θ - cO θ))
    (g₁ : A₁ →ₗ[O] A₁) (g₂ : A₂ →ₗ[O] A₂) (σ₁ : A₁ →ₛₗ[cO] A₁) (σ₂ : A₂ →ₛₗ[cO] A₂)
    (hg₁ : M₁ ≤ M₁.comap g₁) (hg₂ : M₂ ≤ M₂.comap g₂) (hs₁ : M₁ ≤ M₁.comap σ₁) (hs₂ : M₂ ≤ M₂.comap σ₂)
    (hσ₁ : ∀ x, σ₁ (σ₁ x) = x) (hσ₂ : ∀ x, σ₂ (σ₂ x) = x)
    (hc₁ : ∀ x, σ₁ (g₁ x) = g₁ (σ₁ x)) (hc₂ : ∀ x, σ₂ (g₂ x) = g₂ (σ₂ x)) :
    Nat.card {M : Submodule O (A₁ × A₂) // ((∀ y ∈ M, (g₁ y.1, g₂ y.2) ∈ M) ∧
      ∀ y ∈ M, (σ₁ y.1, σ₂ y.2) ∈ M) ∧ Ext M₁ M₂ M} ^ 2 =
    Nat.card {M : Submodule O (A₁ × A₂) // (∀ y ∈ M, (g₁ y.1, g₂ y.2) ∈ M) ∧ Ext M₁ M₂ M} := by
  set Q := compat g₁ g₂ hg₁ hg₂
  let τQ : Q →+ Q :=
    { toFun := fun f => ⟨twist hcc σ₁ σ₂ hs₁ hs₂ f.1, twist_mem hcc σ₁ σ₂ hs₁ hs₂ g₁ g₂ hg₁ hg₂ hc₁ hc₂ f.2⟩
      map_zero' := Subtype.ext (map_zero (twistHom hcc σ₁ σ₂ hs₁ hs₂))
      map_add' := fun f f' => Subtype.ext (map_add (twistHom hcc σ₁ σ₂ hs₁ hs₂) f.1 f'.1) }
  have hτ : ∀ f : Q, ((τQ f : Q) : M₂ →ₗ[O] A₁ ⧸ M₁) = twist hcc σ₁ σ₂ hs₁ hs₂ f.1 := fun _ => rfl
  set u : O := ((hδ.unit⁻¹ : Oˣ) : O)
  have hcu := conj_inv_eq_neg hcc θ hδ
  have e := halfEquiv τQ (fun f => Subtype.ext (by rw [hτ, hτ, twist_twist hcc σ₁ σ₂ hs₁ hs₂ hσ₁ hσ₂]))
    θ (cO θ) u (fun f => Subtype.ext (by rw [hτ, Submodule.coe_smul, Submodule.coe_smul, hτ, twist_smul]))
    (fun f => Subtype.ext (by
      rw [hτ, Submodule.coe_smul, Submodule.coe_neg, Submodule.coe_smul, hτ, twist_smul, hcu, neg_smul]))
    (fun f => by rw [smul_smul, hδ.val_inv_mul, one_smul])
  have e1 : {M : Submodule O (A₁ × A₂) // (∀ y ∈ M, (g₁ y.1, g₂ y.2) ∈ M) ∧ Ext M₁ M₂ M} ≃ Q :=
    (Equiv.subtypeEquivRight (fun M => and_comm)).trans
      ((Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm.trans
        (Equiv.subtypeEquiv extEquiv (fun M => gstab_iff g₁ g₂ hg₁ hg₂ M.2)))
  have e2 : {M : Submodule O (A₁ × A₂) // ((∀ y ∈ M, (g₁ y.1, g₂ y.2) ∈ M) ∧
      ∀ y ∈ M, (σ₁ y.1, σ₂ y.2) ∈ M) ∧ Ext M₁ M₂ M} ≃ {f : Q // τQ f = f} :=
    (Equiv.subtypeEquivRight (fun M => and_comm)).trans
      ((Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm.trans
        ((Equiv.subtypeEquiv extEquiv (fun M => and_congr (gstab_iff g₁ g₂ hg₁ hg₂ M.2)
          (sstab_iff hcc σ₁ σ₂ hs₁ hs₂ hσ₂ M.2))).trans
        ((Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ Q) (fun f => twist hcc σ₁ σ₂ hs₁ hs₂ f = f)).symm.trans
          (Equiv.subtypeEquivRight (fun f => by rw [Subtype.ext_iff, hτ])))))
  rw [Nat.card_congr e2, Nat.card_congr e1, sq, ← Nat.card_prod, Nat.card_congr e]
end GlobalTheory.SigmaExtCount
