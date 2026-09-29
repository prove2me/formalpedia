-- Prove2me | solution 1 for ModularCurve.FullLevel.cuspidalSpecialization_comp_eq_tateProdRep_comp_of_laws
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/97190c44-de85-5a6e-ac35-584fc488f192

import Definitions.Def_ModularCurve_FullLevelCuspidalSpecialization
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_cuspidalSpecialization_comp_eq_tateProdRep_comp_of_laws

set_option autoImplicit false

open scoped TensorProduct
open ModularCurve ModularCurve.FullLevel

namespace LawAAsm

set_option maxHeartbeats 1600000 in

theorem tateRep_one_tmul
    (q : ℕ) [Fact q.Prime] (lam : ℕ) [Fact lam.Prime]
    (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsDomain (DrinfeldCurve.CoordRing q k)]
    (h : ↥(DrinfeldCurve.hSubgroup q))
    (z : RationalTateModule lam (AlgebraicCurve.Pic0 k (DrinfeldCurve.drinfeldFunctionField q k))) :
    DrinfeldCurve.tateRep q k lam ℚ_[lam] h ((1 : ℚ_[lam]) ⊗ₜ[ℚ_[lam]] z) =
      (1 : ℚ_[lam]) ⊗ₜ[ℚ_[lam]] ModularCurve.rationalGaloisRep lam (AlgebraicCurve.Pic0 k (DrinfeldCurve.drinfeldFunctionField q k))
        (DrinfeldCurve.drinfeldFunctionField q k ≃ₐ[k] DrinfeldCurve.drinfeldFunctionField q k)
        (DrinfeldCurve.hFunctionFieldAction q k h) z := by
  change ((ModularCurve.rationalGaloisRep lam (AlgebraicCurve.Pic0 k (DrinfeldCurve.drinfeldFunctionField q k))
        (DrinfeldCurve.drinfeldFunctionField q k ≃ₐ[k] DrinfeldCurve.drinfeldFunctionField q k)
        (DrinfeldCurve.hFunctionFieldAction q k h)).baseChange ℚ_[lam]) ((1 : ℚ_[lam]) ⊗ₜ[ℚ_[lam]] z) = _
  rw [LinearMap.baseChange_tmul]

set_option maxHeartbeats 3200000 in

theorem red_factor_eq
    (q : ℕ) [Fact q.Prime] (M' : ℕ) (lam : ℕ) [Fact lam.Prime]
    (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsDomain (DrinfeldCurve.CoordRing q k)]
    (Ψ : TateModule lam (Jac q M') ≃ₗ[ℤ_[lam]] (Idx q → TateModule lam (jacComp q M')))
    (eC : RationalTateModule lam (Jac q M') →ₗ[ℚ_[lam]] RationalTateModule lam (Jac q M'))
    (Vinv : Submodule ℚ_[lam] (RationalTateModule lam (jacComp q M')))
    (eInv : RationalTateModule lam (jacComp q M') →ₗ[ℚ_[lam]] ↥Vinv)
    {n : ℕ} {Y : Fin n → Type*} [∀ i, AddCommGroup (Y i)] [∀ i, Module ℚ_[lam] (Y i)]
    (red : ↥Vinv →ₗ[ℚ_[lam]] ((i : Fin n) → Y i))
    {T : Type} (c : T → Fin n)
    (Φ : (ζ : Idx q) → (t : T) →
      (Y (c t) →ₗ[ℚ_[lam]] RationalTateModule lam (AlgebraicCurve.Pic0 k (DrinfeldCurve.drinfeldFunctionField q k))))
    (Op : RationalTateModule lam (Jac q M') →ₗ[ℚ_[lam]] RationalTateModule lam (Jac q M'))
    (h : ↥(DrinfeldCurve.hSubgroup q))
    (A : Idx q → (RationalTateModule lam (jacComp q M') →ₗ[ℚ_[lam]] RationalTateModule lam (jacComp q M')))
    (B : (ζ : Idx q) → (t : T) → (Y (c t) →ₗ[ℚ_[lam]] Y (c t)))
    (hEC : eC ∘ₗ Op = Op ∘ₗ eC)
    (hCOORD : ∀ ζ : Idx q, ratCoord q M' lam Ψ ζ ∘ₗ Op = A ζ ∘ₗ ratCoord q M' lam Ψ ζ)
    (hINV : ∀ (v : RationalTateModule lam (Jac q M')) (ζ : Idx q), ratCoord q M' lam Ψ ζ (eC v) ∈ Vinv)
    (hRETR : ∀ w : ↥Vinv, eInv (w : RationalTateModule lam (jacComp q M')) = w)
    (hSTAB : ∀ (ζ : Idx q) (w : RationalTateModule lam (jacComp q M')), w ∈ Vinv → A ζ w ∈ Vinv)
    (hRED : ∀ (ζ : Idx q) (t : T) (w : ↥Vinv),
      red ⟨A ζ (w : RationalTateModule lam (jacComp q M')), hSTAB ζ w w.2⟩ (c t) = B ζ t (red w (c t)))
    (hPHI : ∀ (ζ : Idx q) (t : T),
      Φ ζ t ∘ₗ B ζ t =
        ModularCurve.rationalGaloisRep lam (AlgebraicCurve.Pic0 k (DrinfeldCurve.drinfeldFunctionField q k))
            (DrinfeldCurve.drinfeldFunctionField q k ≃ₐ[k] DrinfeldCurve.drinfeldFunctionField q k)
            (DrinfeldCurve.hFunctionFieldAction q k h) ∘ₗ Φ ζ t)
    (v : RationalTateModule lam (Jac q M')) (ζ : Idx q) (t : T) :
    red (eInv (ratCoord q M' lam Ψ ζ (eC (Op v)))) (c t) =
      B ζ t (red (eInv (ratCoord q M' lam Ψ ζ (eC v))) (c t)) := by
  have hw : ratCoord q M' lam Ψ ζ (eC v) ∈ Vinv := hINV v ζ
  have e1 : ratCoord q M' lam Ψ ζ (eC (Op v)) = A ζ (ratCoord q M' lam Ψ ζ (eC v)) := by
    rw [show eC (Op v) = Op (eC v) from LinearMap.congr_fun hEC v]
    exact LinearMap.congr_fun (hCOORD ζ) (eC v)
  have e2 : eInv (ratCoord q M' lam Ψ ζ (eC (Op v))) =
      ⟨A ζ (ratCoord q M' lam Ψ ζ (eC v)), hSTAB ζ _ hw⟩ := by
    rw [e1]; exact hRETR ⟨_, hSTAB ζ _ hw⟩
  have e3 : eInv (ratCoord q M' lam Ψ ζ (eC v)) = ⟨ratCoord q M' lam Ψ ζ (eC v), hw⟩ := hRETR ⟨_, hw⟩
  rw [e2, e3]
  exact hRED ζ t ⟨ratCoord q M' lam Ψ ζ (eC v), hw⟩

set_option maxHeartbeats 3200000 in

theorem phi_factor_eq
    (q : ℕ) [Fact q.Prime] (M' : ℕ) (lam : ℕ) [Fact lam.Prime]
    (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsDomain (DrinfeldCurve.CoordRing q k)]
    (Ψ : TateModule lam (Jac q M') ≃ₗ[ℤ_[lam]] (Idx q → TateModule lam (jacComp q M')))
    (eC : RationalTateModule lam (Jac q M') →ₗ[ℚ_[lam]] RationalTateModule lam (Jac q M'))
    (Vinv : Submodule ℚ_[lam] (RationalTateModule lam (jacComp q M')))
    (eInv : RationalTateModule lam (jacComp q M') →ₗ[ℚ_[lam]] ↥Vinv)
    {n : ℕ} {Y : Fin n → Type*} [∀ i, AddCommGroup (Y i)] [∀ i, Module ℚ_[lam] (Y i)]
    (red : ↥Vinv →ₗ[ℚ_[lam]] ((i : Fin n) → Y i))
    {T : Type} (c : T → Fin n)
    (Φ : (ζ : Idx q) → (t : T) →
      (Y (c t) →ₗ[ℚ_[lam]] RationalTateModule lam (AlgebraicCurve.Pic0 k (DrinfeldCurve.drinfeldFunctionField q k))))
    (Op : RationalTateModule lam (Jac q M') →ₗ[ℚ_[lam]] RationalTateModule lam (Jac q M'))
    (h : ↥(DrinfeldCurve.hSubgroup q))
    (A : Idx q → (RationalTateModule lam (jacComp q M') →ₗ[ℚ_[lam]] RationalTateModule lam (jacComp q M')))
    (B : (ζ : Idx q) → (t : T) → (Y (c t) →ₗ[ℚ_[lam]] Y (c t)))
    (hEC : eC ∘ₗ Op = Op ∘ₗ eC)
    (hCOORD : ∀ ζ : Idx q, ratCoord q M' lam Ψ ζ ∘ₗ Op = A ζ ∘ₗ ratCoord q M' lam Ψ ζ)
    (hINV : ∀ (v : RationalTateModule lam (Jac q M')) (ζ : Idx q), ratCoord q M' lam Ψ ζ (eC v) ∈ Vinv)
    (hRETR : ∀ w : ↥Vinv, eInv (w : RationalTateModule lam (jacComp q M')) = w)
    (hSTAB : ∀ (ζ : Idx q) (w : RationalTateModule lam (jacComp q M')), w ∈ Vinv → A ζ w ∈ Vinv)
    (hRED : ∀ (ζ : Idx q) (t : T) (w : ↥Vinv),
      red ⟨A ζ (w : RationalTateModule lam (jacComp q M')), hSTAB ζ w w.2⟩ (c t) = B ζ t (red w (c t)))
    (hPHI : ∀ (ζ : Idx q) (t : T),
      Φ ζ t ∘ₗ B ζ t =
        ModularCurve.rationalGaloisRep lam (AlgebraicCurve.Pic0 k (DrinfeldCurve.drinfeldFunctionField q k))
            (DrinfeldCurve.drinfeldFunctionField q k ≃ₐ[k] DrinfeldCurve.drinfeldFunctionField q k)
            (DrinfeldCurve.hFunctionFieldAction q k h) ∘ₗ Φ ζ t)
    (v : RationalTateModule lam (Jac q M')) (ζ : Idx q) (t : T) :
    Φ ζ t (red (eInv (ratCoord q M' lam Ψ ζ (eC (Op v)))) (c t)) =
      ModularCurve.rationalGaloisRep lam (AlgebraicCurve.Pic0 k (DrinfeldCurve.drinfeldFunctionField q k))
        (DrinfeldCurve.drinfeldFunctionField q k ≃ₐ[k] DrinfeldCurve.drinfeldFunctionField q k)
        (DrinfeldCurve.hFunctionFieldAction q k h) (Φ ζ t (red (eInv (ratCoord q M' lam Ψ ζ (eC v))) (c t))) := by
  rw [red_factor_eq q M' lam k Ψ eC Vinv eInv red c Φ Op h A B hEC hCOORD hINV hRETR hSTAB hRED hPHI v ζ t]
  exact LinearMap.congr_fun (hPHI ζ t) _

end LawAAsm

set_option maxHeartbeats 3200000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) (lam : ℕ) [Fact lam.Prime]
    (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsDomain (DrinfeldCurve.CoordRing q k)]
    (Ψ : TateModule lam (Jac q M') ≃ₗ[ℤ_[lam]] (Idx q → TateModule lam (jacComp q M')))
    (eC : RationalTateModule lam (Jac q M') →ₗ[ℚ_[lam]] RationalTateModule lam (Jac q M'))
    (Vinv : Submodule ℚ_[lam] (RationalTateModule lam (jacComp q M')))
    (eInv : RationalTateModule lam (jacComp q M') →ₗ[ℚ_[lam]] ↥Vinv)
    {n : ℕ} {Y : Fin n → Type*} [∀ i, AddCommGroup (Y i)] [∀ i, Module ℚ_[lam] (Y i)]
    (red : ↥Vinv →ₗ[ℚ_[lam]] ((i : Fin n) → Y i))
    {T : Type} (c : T → Fin n)
    (Φ : (ζ : Idx q) → (t : T) →
      (Y (c t) →ₗ[ℚ_[lam]] RationalTateModule lam (AlgebraicCurve.Pic0 k (DrinfeldCurve.drinfeldFunctionField q k))))
    (Op : RationalTateModule lam (Jac q M') →ₗ[ℚ_[lam]] RationalTateModule lam (Jac q M'))
    (h : ↥(DrinfeldCurve.hSubgroup q))
    (A : Idx q → (RationalTateModule lam (jacComp q M') →ₗ[ℚ_[lam]] RationalTateModule lam (jacComp q M')))
    (B : (ζ : Idx q) → (t : T) → (Y (c t) →ₗ[ℚ_[lam]] Y (c t)))
    (hEC : eC ∘ₗ Op = Op ∘ₗ eC)
    (hCOORD : ∀ ζ : Idx q, ratCoord q M' lam Ψ ζ ∘ₗ Op = A ζ ∘ₗ ratCoord q M' lam Ψ ζ)
    (hINV : ∀ (v : RationalTateModule lam (Jac q M')) (ζ : Idx q), ratCoord q M' lam Ψ ζ (eC v) ∈ Vinv)
    (hRETR : ∀ w : ↥Vinv, eInv (w : RationalTateModule lam (jacComp q M')) = w)
    (hSTAB : ∀ (ζ : Idx q) (w : RationalTateModule lam (jacComp q M')), w ∈ Vinv → A ζ w ∈ Vinv)
    (hRED : ∀ (ζ : Idx q) (t : T) (w : ↥Vinv),
      red ⟨A ζ (w : RationalTateModule lam (jacComp q M')), hSTAB ζ w w.2⟩ (c t) = B ζ t (red w (c t)))
    (hPHI : ∀ (ζ : Idx q) (t : T),
      Φ ζ t ∘ₗ B ζ t =
        ModularCurve.rationalGaloisRep lam (AlgebraicCurve.Pic0 k (DrinfeldCurve.drinfeldFunctionField q k))
            (DrinfeldCurve.drinfeldFunctionField q k ≃ₐ[k] DrinfeldCurve.drinfeldFunctionField q k)
            (DrinfeldCurve.hFunctionFieldAction q k h) ∘ₗ Φ ζ t) :
    cuspidalSpecialization q M' lam k Ψ eC Vinv eInv red c Φ ∘ₗ Op =
      DrinfeldCurve.tateProdRep q k lam ℚ_[lam] (Idx q × T) h ∘ₗ
        cuspidalSpecialization q M' lam k Ψ eC Vinv eInv red c Φ := by
  refine LinearMap.ext fun v => ?_
  refine funext fun p => ?_
  obtain ⟨ζ, t⟩ := p
  rw [LinearMap.comp_apply, LinearMap.comp_apply, DrinfeldCurve.tateProdRep_apply,
    cuspidalSpecialization_apply, cuspidalSpecialization_apply, LawAAsm.tateRep_one_tmul,
    LawAAsm.phi_factor_eq q M' lam k Ψ eC Vinv eInv red c Φ Op h A B hEC hCOORD hINV hRETR hSTAB hRED hPHI v ζ t]

end S_ModularCurve_FullLevel_cuspidalSpecialization_comp_eq_tateProdRep_comp_of_laws
end P2MW
export P2MW.S_ModularCurve_FullLevel_cuspidalSpecialization_comp_eq_tateProdRep_comp_of_laws (solution)
