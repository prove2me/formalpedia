-- Prove2me | solution 1 for HopfAlgebra.exists_finiteFlat_padicInt_withConv_equiv_subquotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/7d66faeb-ad81-510d-99ff-4b1c85a56bf1

import Mathlib
import Theorems.Thm_HopfAlgebra_exists_quotientFlag_of_galoisStableChain_of_fixedPoints
import Theorems.Thm_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero
import Theorems.Thm_HopfAlgebra_exists_finiteFlat_padicInt_quotient_of_equivariant_surjection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_finiteFlat_padicInt_withConv_equiv_subquotient
p2m_attr_erase "instance" "GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.Point.instFinite instIsScalarTowerTensorProduct_definitions"
p2m_attr_erase "simp" "GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff"

set_option autoImplicit false
set_option maxHeartbeats 3200000

namespace S17A3

theorem main
    (p : ℕ) [Fact p.Prime]
    (C : Type) [CommRing C] [HopfAlgebra ℤ_[p] C] [Module.Finite ℤ_[p] C] [Module.Flat ℤ_[p] C]
    [Coalgebra.IsCocomm ℤ_[p] C]
    {P : Type} [AddCommGroup P] [DistribMulAction (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) P]
    (eC : WithConv (C →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃ P)
    (heC_add : ∀ f g, eC (f * g) = eC f + eC g)
    (heC_act : ∀ (σ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])) (f g : WithConv (C →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
      (∀ x : C, g x = σ (f x)) → eC g = σ • (eC f))
    (P' : AddSubgroup P) (hP' : ∀ (σ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])) (x : P), x ∈ P' → σ • x ∈ P')
    {N : Type} [AddCommGroup N] [DistribMulAction (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) N]
    (π : ↥P' →+ N) (hπ : Function.Surjective π)
    (hπ_act : ∀ (σ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])) (x : ↥P'), π ⟨σ • (x : P), hP' σ x x.2⟩ = σ • π x) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      ∃ e : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃ N,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]))
          (f g : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
          (∀ x : H, g x = σ (f x)) → e g = σ • (e f)  := by
  classical

  haveI : IsAlgClosure ℚ_[p] (AlgebraicClosure ℚ_[p]) := inferInstance
  haveI : Normal ℚ_[p] (AlgebraicClosure ℚ_[p]) := IsAlgClosure.normal ℚ_[p] (AlgebraicClosure ℚ_[p])
  haveI : IsGalois ℚ_[p] (AlgebraicClosure ℚ_[p]) := IsGalois.mk
  have hfixQ : ∀ c : AlgebraicClosure ℚ_[p], (∀ σ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]), (∀ r : ℤ_[p], σ (algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]) r) = algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]) r) → σ c = c) →
      ∃ a b : ℤ_[p], algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]) b ≠ 0 ∧ c * algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]) b = algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]) a := by
    intro c hc
    have hc' : ∀ σ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]), σ c = c := fun σ =>
      hc σ (fun r => ((σ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])).toAlgHom.restrictScalars ℤ_[p]).commutes r)
    obtain ⟨y, hy⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed c).mpr hc'
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := ℤ_[p]) y
    have hb0 : algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]) b ≠ 0 := by
      rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (AlgebraicClosure ℚ_[p])]
      exact (map_ne_zero _).mpr (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb)
    refine ⟨a, b, hb0, ?_⟩
    rw [← hy, ← hab, IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (AlgebraicClosure ℚ_[p]) a,
      IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (AlgebraicClosure ℚ_[p]) b, ← map_mul, div_mul_cancel₀]
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hinjZ : Function.Injective (algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p])) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] (AlgebraicClosure ℚ_[p]), RingHom.coe_comp]
    exact (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])).injective.comp (IsFractionRing.injective ℤ_[p] ℚ_[p])

  haveI : Module.Free ℤ_[p] C := Module.free_of_flat_of_isLocalRing
  let f₀ : C →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p] := WithConv.ofConv (1 : WithConv (C →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]))
  haveI : Nontrivial C := ⟨⟨1, 0, fun h => one_ne_zero (by rw [← map_one f₀, h, map_zero])⟩⟩
  have hcardpts : Nat.card (C →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) = Module.finrank ℤ_[p] C :=
    HopfAlgebra.natCard_algHom_eq_finrank_of_charZero ℤ_[p] C (AlgebraicClosure ℚ_[p])
  haveI : Finite (C →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) :=
    Nat.finite_of_card_ne_zero (by rw [hcardpts]; exact ((Module.finrank_pos_iff_of_free (R := ℤ_[p]) C).mpr inferInstance).ne')
  haveI : Finite (WithConv (C →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])) := Finite.of_equiv _ (⟨WithConv.ofConv, WithConv.toConv, fun _ => rfl, fun _ => rfl⟩ :
    WithConv (C →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃ (C →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])).symm
  haveI : Finite P := Finite.of_equiv _ eC

  let act : ((AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])) → P → P := fun σ x => σ • x
  have hactC : ∀ (σ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])) (f g : WithConv (C →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])), (∀ x : C, g x = σ (f x)) → eC g = act σ (eC f) := heC_act
  let Nc : Fin (1 + 1) → AddSubgroup P := fun i => if (i : ℕ) = 0 then P' else ⊤
  have hNc : ∀ i, Nc i = if (i : ℕ) = 0 then P' else ⊤ := fun _ => rfl
  have h0 : ((0 : Fin (1 + 1)) : ℕ) = 0 := rfl
  have hmono : ∀ i : Fin 1, Nc i.castSucc ≤ Nc i.succ := by
    intro i
    have h1 : ((i.succ : Fin (1 + 1)) : ℕ) ≠ 0 := by rw [Fin.val_succ]; exact Nat.succ_ne_zero _
    rw [hNc i.succ, if_neg h1]
    exact le_top
  have htop : Nc (Fin.last 1) = ⊤ := by
    rw [hNc, if_neg (show ((Fin.last 1 : Fin (1 + 1)) : ℕ) ≠ 0 by decide)]
  have hstab : ∀ (i : Fin (1 + 1)) (σ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])) (x : P), x ∈ Nc i → act σ x ∈ Nc i := by
    intro i σ x hx
    rw [hNc] at hx ⊢
    by_cases hi : (i : ℕ) = 0
    · rw [if_pos hi] at hx ⊢
      exact hP' σ x hx
    · rw [if_neg hi] at hx ⊢
      exact AddSubgroup.mem_top _
  obtain ⟨B, instCR, instHA, πB, -, -, hflat, hπsurj, -, -, -, hfactor, hcocomm, hfin⟩ :=
    HopfAlgebra.exists_quotientFlag_of_galoisStableChain_of_fixedPoints ℤ_[p] hinjZ hfixQ
      C P eC heC_add act hactC 1 Nc hmono htop hstab
  haveI : Module.Flat ℤ_[p] (B 0) := hflat 0
  haveI : Module.Finite ℤ_[p] (B 0) := (hfin inferInstance 0).1
  haveI : Coalgebra.IsCocomm ℤ_[p] (B 0) := hcocomm inferInstance 0
  let π₀ : C →ₐc[ℤ_[p]] B 0 := πB 0
  have hfac : ∀ g : C →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p],
      (∃ g' : B 0 →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p], g'.comp (π₀ : C →ₐ[ℤ_[p]] B 0) = g) ↔ eC (WithConv.toConv g) ∈ P' := by
    intro g
    rw [hfactor 0 g, hNc, if_pos h0]

  let toC : WithConv (B 0 →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) → WithConv (C →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) := fun g =>
    WithConv.toConv ((WithConv.ofConv g).comp (π₀ : C →ₐ[ℤ_[p]] B 0))
  have htoC : ∀ g, toC g = WithConv.toConv ((WithConv.ofConv g).comp (π₀ : C →ₐ[ℤ_[p]] B 0)) := fun _ => rfl
  have htoC_mem : ∀ g, eC (toC g) ∈ P' := fun g => (hfac _).mp ⟨WithConv.ofConv g, rfl⟩
  have htoC_mul : ∀ g h, toC (g * h) = toC g * toC h := by
    intro g h
    apply WithConv.ext
    show (WithConv.ofConv (g * h)).comp (π₀ : C →ₐ[ℤ_[p]] B 0) = _
    rw [AlgHom.convMul_comp_bialgHom_distrib]
    try rfl
  have htoC_inj : Function.Injective toC := by
    intro g h hgh
    have h1 : (WithConv.ofConv g).comp (π₀ : C →ₐ[ℤ_[p]] B 0) = (WithConv.ofConv h).comp (π₀ : C →ₐ[ℤ_[p]] B 0) :=
      congrArg WithConv.ofConv hgh
    apply WithConv.ext
    exact AlgHom.cancel_right (hπsurj 0) |>.mp h1
  let e' : WithConv (B 0 →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃ ↥P' :=
    Equiv.ofBijective (fun g => ⟨eC (toC g), htoC_mem g⟩) (by
      constructor
      · intro g h hgh
        exact htoC_inj (eC.injective (congrArg Subtype.val hgh))
      · rintro ⟨x, hx⟩
        obtain ⟨g', hg'⟩ := (hfac (WithConv.ofConv (eC.symm x))).mpr (by simpa using hx)
        refine ⟨WithConv.toConv g', Subtype.ext ?_⟩
        show eC (toC (WithConv.toConv g')) = x
        rw [htoC, WithConv.ofConv_toConv, hg', WithConv.toConv_ofConv, Equiv.apply_symm_apply])
  have he'_val : ∀ g, ((e' g : ↥P') : P) = eC (toC g) := fun _ => rfl
  have he'_add : ∀ g h, e' (g * h) = e' g + e' h := by
    intro g h
    apply Subtype.ext
    show eC (toC (g * h)) = eC (toC g) + eC (toC h)
    rw [htoC_mul, heC_add]

  letI : SMul ((AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])) ↥P' := ⟨fun σ x => ⟨σ • (x : P), hP' σ x x.2⟩⟩
  have hsmul_val : ∀ (σ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])) (x : ↥P'), ((σ • x : ↥P') : P) = σ • (x : P) := fun _ _ => rfl
  letI : MulAction ((AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])) ↥P' :=
    { one_smul := fun x => Subtype.ext (by rw [hsmul_val, one_smul])
      mul_smul := fun σ τ x => Subtype.ext (by rw [hsmul_val, hsmul_val, hsmul_val, mul_smul]) }
  letI : DistribMulAction ((AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])) ↥P' :=
    { smul_zero := fun σ => Subtype.ext (by rw [hsmul_val, ZeroMemClass.coe_zero, smul_zero])
      smul_add := fun σ x y => Subtype.ext (by
        rw [hsmul_val, AddMemClass.coe_add, smul_add, AddMemClass.coe_add, hsmul_val, hsmul_val]) }
  have he'_act : ∀ (σ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])) (f g : WithConv (B 0 →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
      (∀ x : B 0, g x = σ (f x)) → e' g = σ • (e' f) := by
    intro σ f g hfg
    apply Subtype.ext
    rw [hsmul_val, he'_val, he'_val]
    apply heC_act σ (toC f) (toC g)
    intro x
    exact hfg (π₀ x)
  have hπ_eq : ∀ (σ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])) (m : ↥P'), π (σ • m) = σ • (π m) := fun σ m => hπ_act σ m

  exact HopfAlgebra.exists_finiteFlat_padicInt_quotient_of_equivariant_surjection p (B 0)
    e' he'_add he'_act π hπ hπ_eq

end S17A3

theorem solution
    (p : ℕ) [Fact p.Prime]
    (C : Type) [CommRing C] [HopfAlgebra ℤ_[p] C] [Module.Finite ℤ_[p] C] [Module.Flat ℤ_[p] C]
    [Coalgebra.IsCocomm ℤ_[p] C]
    {P : Type} [AddCommGroup P] [DistribMulAction (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) P]
    (eC : WithConv (C →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃ P)
    (heC_add : ∀ f g, eC (f * g) = eC f + eC g)
    (heC_act : ∀ (σ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])) (f g : WithConv (C →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
      (∀ x : C, g x = σ (f x)) → eC g = σ • (eC f))
    (P' : AddSubgroup P) (hP' : ∀ (σ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])) (x : P), x ∈ P' → σ • x ∈ P')
    {N : Type} [AddCommGroup N] [DistribMulAction (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) N]
    (π : ↥P' →+ N) (hπ : Function.Surjective π)
    (hπ_act : ∀ (σ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])) (x : ↥P'), π ⟨σ • (x : P), hP' σ x x.2⟩ = σ • π x) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      ∃ e : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃ N,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]))
          (f g : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
          (∀ x : H, g x = σ (f x)) → e g = σ • (e f) :=
  S17A3.main p C eC heC_add heC_act P' hP' π hπ hπ_act

end S_HopfAlgebra_exists_finiteFlat_padicInt_withConv_equiv_subquotient
end P2MW
export P2MW.S_HopfAlgebra_exists_finiteFlat_padicInt_withConv_equiv_subquotient (solution)
