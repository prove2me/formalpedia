-- Prove2me | solution 1 for HopfAlgebra.bialgHom_eq_of_forall_algHom_comp_eq_of_charZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/ac326660-d61e-584b-87f2-18a34b9d7a4f

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_PDivisibleGroup_Points
import Theorems.Thm_HopfAlgebra_existsUnique_bialgHom_forall_apply_comp_eq_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_bialgHom_eq_of_forall_algHom_comp_eq_of_charZero

set_option autoImplicit false

namespace AGREE

variable (K : Type) [Field K] (Kbar : Type) [Field Kbar] [Algebra K Kbar]

@[reducible] noncomputable def galAction (E : Type) [CommRing E] [HopfAlgebra K E] :
    DistribMulAction (Kbar ≃ₐ[K] Kbar) (Additive (WithConv (E →ₐ[K] Kbar))) where
  smul σ a := Additive.ofMul (WithConv.toConv ((σ : Kbar →ₐ[K] Kbar).comp (WithConv.ofConv (Additive.toMul a))))
  one_smul a := rfl
  mul_smul σ τ a := rfl
  smul_zero σ := by
    change Additive.ofMul (WithConv.toConv ((σ : Kbar →ₐ[K] Kbar).comp (WithConv.ofConv (1 : WithConv (E →ₐ[K] Kbar))))) =
      Additive.ofMul (1 : WithConv (E →ₐ[K] Kbar))
    apply congrArg Additive.ofMul
    apply WithConv.ext
    change (σ : Kbar →ₐ[K] Kbar).comp (WithConv.ofConv (1 : WithConv (E →ₐ[K] Kbar))) = WithConv.ofConv (1 : WithConv (E →ₐ[K] Kbar))
    rw [AlgHom.convOne_def]
    change (σ : Kbar →ₐ[K] Kbar).comp ((Algebra.ofId K Kbar).comp (Bialgebra.counitAlgHom K E)) =
      (Algebra.ofId K Kbar).comp (Bialgebra.counitAlgHom K E)
    rw [← AlgHom.comp_assoc, Algebra.comp_ofId]
  smul_add σ a b := by
    change Additive.ofMul (WithConv.toConv ((σ : Kbar →ₐ[K] Kbar).comp (WithConv.ofConv (Additive.toMul a * Additive.toMul b)))) =
      Additive.ofMul (WithConv.toConv ((σ : Kbar →ₐ[K] Kbar).comp (WithConv.ofConv (Additive.toMul a))) *
        WithConv.toConv ((σ : Kbar →ₐ[K] Kbar).comp (WithConv.ofConv (Additive.toMul b))))
    apply congrArg Additive.ofMul
    apply WithConv.ofConv_injective
    exact AlgHom.comp_convMul_distrib (σ : Kbar →ₐ[K] Kbar) (Additive.toMul a) (Additive.toMul b)

theorem galAction_smul_def (E : Type) [CommRing E] [HopfAlgebra K E] (σ : Kbar ≃ₐ[K] Kbar) (a : Additive (WithConv (E →ₐ[K] Kbar))) :
    (letI := galAction K Kbar E; σ • a) =
      Additive.ofMul (WithConv.toConv ((σ : Kbar →ₐ[K] Kbar).comp (WithConv.ofConv (Additive.toMul a)))) := rfl

end AGREE

open AGREE in
theorem solution
    (K : Type) [Field K] [CharZero K] (Kbar : Type) [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar]
    (E₁ : Type) [CommRing E₁] [HopfAlgebra K E₁] [Coalgebra.IsCocomm K E₁] [Module.Finite K E₁]
    (E₂ : Type) [CommRing E₂] [HopfAlgebra K E₂] [Coalgebra.IsCocomm K E₂] [Module.Finite K E₂]
    (ψ ψ' : E₂ →ₐc[K] E₁)
    (h : ∀ f : E₁ →ₐ[K] Kbar, f.comp (ψ : E₂ →ₐ[K] E₁) = f.comp (ψ' : E₂ →ₐ[K] E₁)) :
    ψ = ψ' := by
  classical

  letI : CommGroup (WithConv (E₁ →ₐ[K] Kbar)) :=
    commGroupOfIsUnit fun x => PDivisibleGroup.Hopf.isUnit_toConv_algHom (WithConv.ofConv x)
  letI : CommGroup (WithConv (E₂ →ₐ[K] Kbar)) :=
    commGroupOfIsUnit fun x => PDivisibleGroup.Hopf.isUnit_toConv_algHom (WithConv.ofConv x)
  letI := galAction K Kbar E₁
  letI := galAction K Kbar E₂

  let φM : Additive (WithConv (E₁ →ₐ[K] Kbar)) →+ Additive (WithConv (E₂ →ₐ[K] Kbar)) :=
    (PDivisibleGroup.Hopf.convCompMonoidHom Kbar ψ).toAdditive
  have hφM : ∀ a, φM a = Additive.ofMul (WithConv.toConv ((WithConv.ofConv (Additive.toMul a)).comp (ψ : E₂ →ₐ[K] E₁))) :=
    fun a => rfl
  have hφgal : ∀ (σ : Kbar ≃ₐ[K] Kbar) (a : Additive (WithConv (E₁ →ₐ[K] Kbar))), φM (σ • a) = σ • φM a := by
    intro σ a; rfl
  obtain ⟨χ, -, huniq⟩ := HopfAlgebra.existsUnique_bialgHom_forall_apply_comp_eq_of_charZero K Kbar
    E₁ (Additive.ofMul : WithConv (E₁ →ₐ[K] Kbar) ≃ Additive (WithConv (E₁ →ₐ[K] Kbar))) (fun _ _ => rfl)
    (fun σ f g hfg => by
      change Additive.ofMul g = Additive.ofMul (WithConv.toConv ((σ : Kbar →ₐ[K] Kbar).comp (WithConv.ofConv f)))
      congr 1
      exact WithConv.ext (AlgHom.ext hfg))
    E₂ (Additive.ofMul : WithConv (E₂ →ₐ[K] Kbar) ≃ Additive (WithConv (E₂ →ₐ[K] Kbar))) (fun _ _ => rfl)
    (fun σ f g hfg => by
      change Additive.ofMul g = Additive.ofMul (WithConv.toConv ((σ : Kbar →ₐ[K] Kbar).comp (WithConv.ofConv f)))
      congr 1
      exact WithConv.ext (AlgHom.ext hfg))
    φM hφgal
  have h1 : ψ = χ := huniq ψ fun f => rfl
  have h2 : ψ' = χ := huniq ψ' fun f => by
    show Additive.ofMul (WithConv.toConv ((WithConv.ofConv f).comp (ψ' : E₂ →ₐ[K] E₁))) =
      Additive.ofMul (WithConv.toConv ((WithConv.ofConv f).comp (ψ : E₂ →ₐ[K] E₁)))
    rw [h (WithConv.ofConv f)]
  rw [h1, h2]

end S_HopfAlgebra_bialgHom_eq_of_forall_algHom_comp_eq_of_charZero
end P2MW
export P2MW.S_HopfAlgebra_bialgHom_eq_of_forall_algHom_comp_eq_of_charZero (solution)
