-- Prove2me | solution 1 for ModularCurve.forall_mem_integers_and_coe_residue_eq_of_tmul_of_forall_coe_eq_coeffMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/0227ae5b-68c6-540b-bb59-40e9a0e7339c

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_forall_mem_integers_and_coe_residue_eq_of_tmul_of_forall_coe_eq_coeffMap

set_option autoImplicit false
open scoped MatrixGroups TensorProduct
open IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel

namespace TensorRead

theorem induction {Rp : Type*} [CommRing Rp] {Pl B : Type*} [CommRing Pl] [CommRing B] [Algebra Rp Pl] [Algebra Rp B]
    {F : Type*} [Field F] (O : ValuationSubring F) {E E' L : Type*} [NonAssocSemiring E] [NonAssocSemiring E']
    [Add L] (res : ↥O →+* E) (φ : E → L) (hφ : ∀ a a' : E, φ (a + a') = φ a + φ a')
    (γ : Pl ⊗[Rp] B →+* F) (r : Pl ⊗[Rp] B →+* E') (ψ : E' → L) (hψ : ∀ a a' : E', ψ (a + a') = ψ a + ψ a')
    (h : ∀ (α : Pl) (b : B), ∃ hO : γ (α ⊗ₜ b) ∈ O, φ (res ⟨_, hO⟩) = ψ (r (α ⊗ₜ b)))
    (t : Pl ⊗[Rp] B) : ∃ hO : γ t ∈ O, φ (res ⟨γ t, hO⟩) = ψ (r t) := by
  suffices hh : ∀ t : Pl ⊗[Rp] B, γ t ∈ O ∧ ∀ hO : γ t ∈ O, φ (res ⟨γ t, hO⟩) = ψ (r t) by
    exact ⟨(hh t).1, (hh t).2 _⟩
  intro t
  induction t using TensorProduct.induction_on with
  | zero =>
      obtain ⟨hO, hres⟩ := h 0 0
      have h0 : ((0 : Pl) ⊗ₜ[Rp] (0 : B)) = 0 := TensorProduct.zero_tmul _ _
      rw [← h0]
      exact ⟨hO, fun _ => hres⟩
  | tmul α b =>
      obtain ⟨hO, hres⟩ := h α b
      exact ⟨hO, fun _ => hres⟩
  | add s t hs ht =>
      obtain ⟨hs1, hs2⟩ := hs
      obtain ⟨ht1, ht2⟩ := ht
      refine ⟨by rw [map_add]; exact add_mem hs1 ht1, fun hO => ?_⟩
      have hsub : (⟨γ (s + t), hO⟩ : ↥O) = ⟨γ s, hs1⟩ + ⟨γ t, ht1⟩ := Subtype.ext (map_add γ s t)
      rw [hsub, map_add, map_add, hφ, hψ, hs2 hs1, ht2 ht1]

theorem smul_coeffEmb_coeffMap_eq (p : ℕ) (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (α : ↥Pl) (y : LaurentSeries (R p)) :
    (α : AlgebraicClosure ℚ) • coeffEmb (AlgebraicClosure ℚ) (coeffMap (algebraMap (R p) ℚ) y) =
      coeffMap Pl.subtype (HahnSeries.C α * coeffMap ρ y) := by
  have hρ' : ∀ z : R p, ((ρ z : ↥Pl) : AlgebraicClosure ℚ) = algebraMap (R p) (AlgebraicClosure ℚ) z :=
    fun z => by simpa using congrArg (fun φ => φ z) hρ
  ext k
  simp only [HahnSeries.coeff_smul, coeffEmb_coeff, coeffMap_coeff, HahnSeries.C_mul_eq_smul, map_mul,
    smul_eq_mul, hρ', ValuationSubring.coe_subtype]
  rfl

theorem coeffMap_residue_C_mul (p : ℕ) (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (ρ : R p →+* ↥Pl) (α : ↥Pl) (y : LaurentSeries (R p)) :
    coeffMap (residue ↥Pl) (HahnSeries.C α * coeffMap ρ y) =
      residue ↥Pl α • coeffMap ((residue ↥Pl).comp ρ) y := by
  ext k
  simp only [coeffMap_coeff, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul, map_mul,
    RingHom.coe_comp, Function.comp_apply]

end TensorRead

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [Algebra (R p) ↥Pl] (halg : algebraMap (R p) ↥Pl = ρ)

    (B : Subalgebra (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)))
    (hlift : ∀ b : ↥B, ∃ y : LaurentSeries (R p),
      coeffMap (algebraMap (R p) ℚ) y = (((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)))

    (r₀ : ↥B →+* ↥(qExpFunctionFieldC (ResidueField ↥Pl) (ΓN p M H hpM)))
    (hr₀ : ∀ (b : ↥B) (y : LaurentSeries (R p)),
      coeffMap (algebraMap (R p) ℚ) y = (((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)) →
      ((r₀ b : ↥(qExpFunctionFieldC (ResidueField ↥Pl) (ΓN p M H hpM))) : LaurentSeries (ResidueField ↥Pl)) =
        coeffMap ((residue ↥Pl).comp ρ) y)

    (Rg : RegularProlongation Pl ↥(xHFunctionFieldBar M H) ↥(qExpFunctionFieldC (ResidueField ↥Pl) (ΓM M H)))
    (hq : ∀ (y : LaurentSeries ↥Pl) (hy : coeffMap Pl.subtype y ∈ xHFunctionFieldBar M H),
      ∃ hO : (⟨coeffMap Pl.subtype y, hy⟩ : ↥(xHFunctionFieldBar M H)) ∈ Rg.integers,
        ((Rg.residue ⟨_, hO⟩ : ↥(qExpFunctionFieldC (ResidueField ↥Pl) (ΓM M H))) : LaurentSeries (ResidueField ↥Pl)) =
          coeffMap (residue ↥Pl) y)

    (γ : ↥Pl ⊗[R p] ↥B →+* ↥(xHFunctionFieldBar M H))
    (hγ : ∀ (α : ↥Pl) (b : ↥B), ((γ (α ⊗ₜ b) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      (α : AlgebraicClosure ℚ) • coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)))
    (r : ↥Pl ⊗[R p] ↥B →+* ↥(qExpFunctionFieldC (ResidueField ↥Pl) (ΓN p M H hpM)))
    (hr : ∀ (α : ↥Pl) (b : ↥B), ((r (α ⊗ₜ b) : ↥(qExpFunctionFieldC (ResidueField ↥Pl) (ΓN p M H hpM))) : LaurentSeries (ResidueField ↥Pl)) =
      residue ↥Pl α • ((r₀ b : ↥(qExpFunctionFieldC (ResidueField ↥Pl) (ΓN p M H hpM))) : LaurentSeries (ResidueField ↥Pl)))
    (t : ↥Pl ⊗[R p] ↥B) :
    ∃ hO : γ t ∈ Rg.integers,
      ((Rg.residue ⟨γ t, hO⟩ : ↥(qExpFunctionFieldC (ResidueField ↥Pl) (ΓM M H))) : LaurentSeries (ResidueField ↥Pl)) =
        ((r t : ↥(qExpFunctionFieldC (ResidueField ↥Pl) (ΓN p M H hpM))) : LaurentSeries (ResidueField ↥Pl)) := by

  revert hq
  obtain ⟨O, res, -, -, -, -, -⟩ := Rg
  intro hq
  dsimp only at hq ⊢
  refine TensorRead.induction O res
    (fun x : ↥(qExpFunctionFieldC (ResidueField ↥Pl) (ΓM M H)) => (x : LaurentSeries (ResidueField ↥Pl)))
    (fun a a' => rfl) γ r
    (fun x : ↥(qExpFunctionFieldC (ResidueField ↥Pl) (ΓN p M H hpM)) => (x : LaurentSeries (ResidueField ↥Pl)))
    (fun a a' => rfl) ?_ t
  intro α b
  obtain ⟨y, hy⟩ := hlift b
  have hcoe : ((γ (α ⊗ₜ b) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffMap Pl.subtype (HahnSeries.C α * coeffMap ρ y) := by
    rw [hγ, ← hy]
    exact TensorRead.smul_coeffEmb_coeffMap_eq p Pl ρ hρ α y
  have hmem : coeffMap Pl.subtype (HahnSeries.C α * coeffMap ρ y) ∈ xHFunctionFieldBar M H :=
    hcoe ▸ (γ (α ⊗ₜ b)).2
  have hq' := hq (HahnSeries.C α * coeffMap ρ y) hmem
  have heq : γ (α ⊗ₜ b) = ⟨coeffMap Pl.subtype (HahnSeries.C α * coeffMap ρ y), hmem⟩ := Subtype.ext hcoe
  have key : ∀ (z : ↥(xHFunctionFieldBar M H)), z = ⟨coeffMap Pl.subtype (HahnSeries.C α * coeffMap ρ y), hmem⟩ →
      ∃ hz : z ∈ O, ((res ⟨z, hz⟩ : ↥(qExpFunctionFieldC (ResidueField ↥Pl) (ΓM M H))) :
        LaurentSeries (ResidueField ↥Pl)) = coeffMap (residue ↥Pl) (HahnSeries.C α * coeffMap ρ y) := by
    rintro z rfl
    exact hq'
  obtain ⟨hz, hres⟩ := key _ heq
  refine ⟨hz, ?_⟩
  rw [hres, hr, hr₀ b y hy]
  exact TensorRead.coeffMap_residue_C_mul p Pl ρ α y

end S_ModularCurve_forall_mem_integers_and_coe_residue_eq_of_tmul_of_forall_coe_eq_coeffMap
end P2MW
export P2MW.S_ModularCurve_forall_mem_integers_and_coe_residue_eq_of_tmul_of_forall_coe_eq_coeffMap (solution)
