-- Prove2me | solution 1 for LevelRaising.exists_parabolicPairings_perfect_mod_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/ec52ca58-c087-5dfb-84e7-b6f3e2d533a0

import Definitions.Def_HeckeEis_DegeneracyTransfers
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_ModularCurve_PDPairing
import Theorems.Thm_ModularCurve_PDPairing_exists_forall_smul_eq_pairZ_and_perfect_mod_three
import Theorems.Thm_ModularCurve_PDPairing_isFreeGroup_Gamma_four
import Theorems.Thm_ModularCurve_PDPairing_pairZFun_heckeT0_comm
import Theorems.Thm_ModularCurve_PDPairing_pairZFun_jDeg0_iDeg0
import Theorems.Thm_HeckeEis_coresHom_eq_transfer
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LevelRaising_exists_parabolicPairings_perfect_mod_three
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false

open CongruenceSubgroup HeckeEis

section CorestrictionSection
open scoped MatrixGroups

namespace Corestriction

section Generic
variable {G : Type*} [Group G] {A : Type*} [AddCommGroup A]

private theorem section_cocycle_mem (H : Subgroup G) (R : G ⧸ H → G) (hR : ∀ q, (R q : G ⧸ H) = q)
    (g : G) (q : G ⧸ H) : (R (g • q))⁻¹ * (g * R q) ∈ H := by
  refine QuotientGroup.eq.mp ?_
  rw [hR (g • q)]
  show g • q = ((g * R q : G) : G ⧸ H)
  rw [show ((g * R q : G) : G ⧸ H) = g • ((R q : G) : G ⧸ H) from rfl, hR q]

private theorem coresHom_apply_section (H : Subgroup G) [H.FiniteIndex] (φ : Additive ↥H →+ A)
    (R : G ⧸ H → G) (hR : ∀ q, (R q : G ⧸ H) = q) (g : G) :
    letI := H.fintypeQuotientOfFiniteIndex
    coresHom H φ (Additive.ofMul g) =
      ∑ q : G ⧸ H, φ (Additive.ofMul
        (⟨(R (g • q))⁻¹ * (g * R q), section_cocycle_mem H R hR g q⟩ : ↥H)) := by
  letI := H.fintypeQuotientOfFiniteIndex
  have hmem : ∀ q : G ⧸ H, (Quotient.out q)⁻¹ * R q ∈ H := fun q => by
    refine QuotientGroup.eq.mp ?_
    rw [QuotientGroup.out_eq', hR q]
  have hsplit : ∀ q : G ⧸ H,
      φ (Additive.ofMul (⟨(R (g • q))⁻¹ * (g * R q), section_cocycle_mem H R hR g q⟩ : ↥H))
        = φ (Additive.ofMul (transferAux H g q))
          + (φ (Additive.ofMul (⟨(Quotient.out q)⁻¹ * R q, hmem q⟩ : ↥H))
             - φ (Additive.ofMul (⟨(Quotient.out (g • q))⁻¹ * R (g • q), hmem (g • q)⟩ : ↥H))) := by
    intro q
    have hdec : (⟨(R (g • q))⁻¹ * (g * R q), section_cocycle_mem H R hR g q⟩ : ↥H)
        = (⟨(Quotient.out (g • q))⁻¹ * R (g • q), hmem (g • q)⟩ : ↥H)⁻¹
            * transferAux H g q * (⟨(Quotient.out q)⁻¹ * R q, hmem q⟩ : ↥H) := by
      ext
      show (R (g • q))⁻¹ * (g * R q)
          = ((Quotient.out (g • q))⁻¹ * R (g • q))⁻¹
              * ((g • q).out⁻¹ * (g * Quotient.out q)) * ((Quotient.out q)⁻¹ * R q)
      group
    rw [hdec, ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg]
    abel
  have hre : ∑ q : G ⧸ H,
      φ (Additive.ofMul (⟨(Quotient.out (g • q))⁻¹ * R (g • q), hmem (g • q)⟩ : ↥H))
        = ∑ q : G ⧸ H, φ (Additive.ofMul (⟨(Quotient.out q)⁻¹ * R q, hmem q⟩ : ↥H)) :=
    Fintype.sum_equiv
      (⟨fun q => g • q, fun q => g⁻¹ • q, fun q => inv_smul_smul g q,
        fun q => smul_inv_smul g q⟩ : (G ⧸ H) ≃ (G ⧸ H))
      _ _ (fun q => rfl)
  have hsec : ∑ q : G ⧸ H, φ (Additive.ofMul
      (⟨(R (g • q))⁻¹ * (g * R q), section_cocycle_mem H R hR g q⟩ : ↥H))
        = ∑ q : G ⧸ H, φ (Additive.ofMul (transferAux H g q)) := by
    rw [Finset.sum_congr rfl (fun q _ => hsplit q), Finset.sum_add_distrib,
      Finset.sum_sub_distrib, hre]
    simp
  rw [coresHom_apply, hsec]

end Generic

section Transport
variable {K G' : Type*} [Group K] [Group G'] {A : Type*} [AddCommGroup A]

private def quotMap (H' : Subgroup G') (σ : K →* G') : K ⧸ (H'.comap σ) → G' ⧸ H' :=
  Quotient.map' σ (fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    simpa [map_mul, map_inv] using hab)

@[scoped simp] private theorem quotMap_mk (H' : Subgroup G') (σ : K →* G') (k : K) :
    quotMap H' σ ((k : K ⧸ (H'.comap σ))) = ((σ k : G') : G' ⧸ H') := rfl

private theorem quotMap_injective (H' : Subgroup G') (σ : K →* G') :
    Function.Injective (quotMap H' σ) := by
  intro a b
  refine Quotient.inductionOn₂' a b (fun x y h => ?_)
  have hxy : (σ x)⁻¹ * σ y ∈ H' := QuotientGroup.eq.mp h
  refine QuotientGroup.eq.mpr ?_
  show x⁻¹ * y ∈ H'.comap σ
  rw [Subgroup.mem_comap, map_mul, map_inv]
  exact hxy

private theorem surj_quotMap_of_surjective {K G' : Type*} [Group K] [Group G'] (H' : Subgroup G')
    (σ : K →* G') (hσ : Function.Surjective σ) : Function.Surjective (quotMap H' σ) := by
  intro s
  refine Quotient.inductionOn' s (fun g' => ?_)
  obtain ⟨k, rfl⟩ := hσ g'
  exact ⟨((k : K) : K ⧸ (H'.comap σ)), rfl⟩

private theorem finiteIndex_comap_of_surjQuot {K G' : Type*} [Group K] [Group G']
    (H' : Subgroup G') [H'.FiniteIndex] (σ : K →* G')
    (hsurj : Function.Surjective (quotMap H' σ)) : (H'.comap σ).FiniteIndex := by
  constructor
  have hcard : Nat.card (K ⧸ (H'.comap σ)) = Nat.card (G' ⧸ H') :=
    Nat.card_eq_of_bijective _ ⟨quotMap_injective H' σ, hsurj⟩
  show (H'.comap σ).index ≠ 0
  rw [Subgroup.index, hcard]
  exact Subgroup.FiniteIndex.index_ne_zero

private theorem coresHom_comp_apply (H' : Subgroup G') [H'.FiniteIndex] (σ : K →* G')
    [(H'.comap σ).FiniteIndex]
    (hsurj : Function.Surjective (quotMap H' σ))
    (ψ : Additive ↥H' →+ A) (k : K) :
    coresHom H' ψ (Additive.ofMul (σ k)) =
      coresHom (H'.comap σ) (ψ.comp (AddMonoidHom.mk'
        (fun j => Additive.ofMul (⟨σ (Additive.toMul j : ↥(H'.comap σ)), (Additive.toMul j).2⟩ : ↥H'))
        (fun a b => by simp [map_mul]; rfl)))
        (Additive.ofMul k) := by
  classical
  letI := H'.fintypeQuotientOfFiniteIndex
  letI := (H'.comap σ).fintypeQuotientOfFiniteIndex
  have hbij : Function.Bijective (quotMap H' σ) := ⟨quotMap_injective H' σ, hsurj⟩
  set e : (K ⧸ (H'.comap σ)) ≃ (G' ⧸ H') := Equiv.ofBijective _ hbij with hedef
  have happ : ∀ w, e w = quotMap H' σ w := fun _ => rfl
  set R : G' ⧸ H' → G' := fun s => σ (Quotient.out (e.symm s)) with hRdef
  have hR : ∀ s, ((R s : G') : G' ⧸ H') = s := by
    intro s
    show ((σ (Quotient.out (e.symm s)) : G') : G' ⧸ H') = s
    have h1 : ((σ (Quotient.out (e.symm s)) : G') : G' ⧸ H')
        = quotMap H' σ ((Quotient.out (e.symm s) : K) : K ⧸ (H'.comap σ)) := rfl
    rw [h1, QuotientGroup.out_eq']
    rw [← happ (e.symm s)]
    exact e.apply_symm_apply s
  rw [coresHom_apply_section H' ψ R hR (σ k), coresHom_apply]
  refine (Fintype.sum_equiv e _ _ ?_).symm
  intro w
  have hsmul : (σ k) • (e w) = e (k • w) := by
    refine Quotient.inductionOn' w (fun a => ?_)
    show ((σ k * σ a : G') : G' ⧸ H') = quotMap H' σ ((k * a : K) : K ⧸ (H'.comap σ))
    rw [quotMap_mk, map_mul]
  have hRew : R (e w) = σ (Quotient.out w) := by
    show σ (Quotient.out (e.symm (e w))) = σ (Quotient.out w)
    rw [e.symm_apply_apply]
  have hRsmul : R ((σ k) • (e w)) = σ (Quotient.out (k • w)) := by
    rw [hsmul]
    show σ (Quotient.out (e.symm (e (k • w)))) = σ (Quotient.out (k • w))
    rw [e.symm_apply_apply]
  refine congrArg ψ (congrArg Additive.ofMul (Subtype.ext ?_))
  show σ ((transferAux (H'.comap σ) k w : ↥(H'.comap σ)) : K)
      = (R ((σ k) • (e w)))⁻¹ * (σ k * R (e w))
  rw [hRew, hRsmul, coe_transferAux]
  rw [map_mul, map_mul, map_inv]

end Transport

section Trans
variable {G : Type*} [Group G] {A : Type*} [AddCommGroup A]

private theorem coresHom_congr {G : Type*} [Group G] {K₁ K₂ : Subgroup G} (h : K₁ = K₂)
    [K₁.FiniteIndex] [K₂.FiniteIndex]
    (f₁ : Additive ↥K₁ →+ A) (f₂ : Additive ↥K₂ →+ A)
    (hf : ∀ (g : G) (h₁ : g ∈ K₁), f₁ (Additive.ofMul (⟨g, h₁⟩ : ↥K₁))
        = f₂ (Additive.ofMul (⟨g, h ▸ h₁⟩ : ↥K₂)))
    (x : Additive G) :
    coresHom K₁ f₁ x = coresHom K₂ f₂ x := by
  subst h
  have hext : f₁ = f₂ := AddMonoidHom.ext fun y => by
    have h := hf (Additive.toMul y : ↥K₁) (Additive.toMul y).2
    simpa using h
  rw [hext]

end Trans

end Corestriction
p2m_reactivate "P2MW.S_LevelRaising_exists_parabolicPairings_perfect_mod_three.Corestriction"

end CorestrictionSection
p2m_reactivate "P2MW.S_LevelRaising_exists_parabolicPairings_perfect_mod_three.Corestriction"

namespace ParabolicPairings

section Transfer0Section
open scoped MatrixGroups

namespace Transfer0

variable (N q' : ℕ) [NeZero N] [NeZero q']

omit [NeZero N] [NeZero q'] in

private theorem iotaDeg0_one_eq_iota0 (γ : Gamma0 (N * q')) :
    ModularCurve.PDPairing.iotaDeg0 N (N * q') 1 (dvd_mul_right N q') (one_dvd _) γ
      = Ihara.ι₀ N q' γ := by
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  show ModularCurve.PDPairing.conjLowerMat 1 (γ : SL(2, ℤ))
        (ModularCurve.PDPairing.dvd_entry0 N (N * q') 1
          (dvd_mul_right N q') (one_dvd _) γ) i j
      = (((Ihara.ι₀ N q' γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j
  have hι : (((Ihara.ι₀ N q' γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := rfl
  rw [hι]
  fin_cases i <;> fin_cases j <;>
    simp [ModularCurve.PDPairing.conjLowerMat]

omit [NeZero N] [NeZero q'] in

private theorem range_iotaDeg0_one :
    (ModularCurve.PDPairing.iotaDeg0 N (N * q') 1 (dvd_mul_right N q') (one_dvd _)).range
      = (Ihara.ι₀ N q').range := by
  ext x
  constructor
  · rintro ⟨γ, rfl⟩
    exact ⟨γ, (iotaDeg0_one_eq_iota0 N q' γ).symm⟩
  · rintro ⟨γ, rfl⟩
    exact ⟨γ, iotaDeg0_one_eq_iota0 N q' γ⟩

omit [NeZero N] in

private theorem heckeUpper_comap_conj_bezout (a b : ℤ) (hab : (q' : ℤ) * a - (N : ℤ) * b = 1) :
    (heckeUpper N q').comap
        (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom
      = (Ihara.ι₀ N q').range := by
  ext x
  constructor
  · intro hx
    have hmem : bezoutConjugator N q' a b hab * x * (bezoutConjugator N q' a b hab)⁻¹
        ∈ heckeUpper N q' := hx
    rw [← range_iota1 N (NeZero.ne q')] at hmem
    obtain ⟨δ, hδ⟩ := hmem
    have hsolve : alConjHom N q' (bezoutConjugator N q' a b hab)
        (bezoutConjugator_heckeUpper_dvd N q' a b hab)
        (alConjHom N q' (bezoutConjugator N q' a b hab)
          (bezoutConjugator_heckeUpper_dvd N q' a b hab)
          ((alConjSqElt N q' a b hab)⁻¹ * δ * alConjSqElt N q' a b hab)) = δ := by
      rw [alConjHom_bezout_sq N q' a b hab]
      group
    have hι₁ : Ihara.ι₁ N q' δ
        = bezoutConjugator N q' a b hab *
            Ihara.ι₀ N q' (alConjHom N q' (bezoutConjugator N q' a b hab)
              (bezoutConjugator_heckeUpper_dvd N q' a b hab)
              ((alConjSqElt N q' a b hab)⁻¹ * δ * alConjSqElt N q' a b hab)) *
            (bezoutConjugator N q' a b hab)⁻¹ := by
      conv_lhs => rw [← hsolve]
      rw [iota1_alConjHom]
    refine ⟨alConjHom N q' (bezoutConjugator N q' a b hab)
      (bezoutConjugator_heckeUpper_dvd N q' a b hab)
      ((alConjSqElt N q' a b hab)⁻¹ * δ * alConjSqElt N q' a b hab), ?_⟩
    have hux : bezoutConjugator N q' a b hab *
        Ihara.ι₀ N q' (alConjHom N q' (bezoutConjugator N q' a b hab)
          (bezoutConjugator_heckeUpper_dvd N q' a b hab)
          ((alConjSqElt N q' a b hab)⁻¹ * δ * alConjSqElt N q' a b hab)) *
        (bezoutConjugator N q' a b hab)⁻¹
        = bezoutConjugator N q' a b hab * x * (bezoutConjugator N q' a b hab)⁻¹ := by
      rw [← hι₁, hδ]
    exact mul_left_cancel (mul_right_cancel hux)
  · rintro ⟨γ, rfl⟩
    show bezoutConjugator N q' a b hab * Ihara.ι₀ N q' γ *
        (bezoutConjugator N q' a b hab)⁻¹ ∈ heckeUpper N q'
    exact (mem_heckeUpper N q').mpr (bezoutConjugator_heckeUpper_dvd N q' a b hab γ)

private theorem jDeg0_one_eq_degeneracyTransfer₀Aux (a b : ℤ)
    (hab : (q' : ℤ) * a - (N : ℤ) * b = 1)
    (φ : Additive (Gamma0 (N * q')) →+ ℤ) (x : Additive (Gamma0 N)) :
    ModularCurve.PDPairing.jDeg0 N (N * q') 1 ℤ ℤ (dvd_mul_right N q') (one_dvd _) φ x
      = degeneracyTransfer₀Aux N q' ℤ (bezoutConjugator N q' a b hab)
          (bezoutConjugator_heckeUpper_dvd N q' a b hab) φ x := by
  classical

  have hB0 : ∀ (K : Subgroup (Gamma0 N)) [K.FiniteIndex] (χ : Additive ↥K →+ ℤ),
      ModularCurve.PDPairing.coresAdd K χ = coresHom K χ := by
    intro K _ χ
    rw [coresHom_eq_transfer]
    rfl
  have hcomap : (heckeUpper N q').comap
      (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom
      = (ModularCurve.PDPairing.iotaDeg0 N (N * q') 1
          (dvd_mul_right N q') (one_dvd _)).range := by
    rw [heckeUpper_comap_conj_bezout N q' a b hab, range_iotaDeg0_one]
  haveI hFIcomap : ((heckeUpper N q').comap
      (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom).FiniteIndex := by
    rw [hcomap]
    exact ModularCurve.PDPairing.iotaDeg0_range_finiteIndex _ _ _ _ _
  have hσsurj : Function.Surjective
      (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom :=
    (MulAut.conj (bezoutConjugator N q' a b hab)).surjective

  have hLHS : ModularCurve.PDPairing.jDeg0 N (N * q') 1 ℤ ℤ
      (dvd_mul_right N q') (one_dvd _) φ x
      = coresHom (ModularCurve.PDPairing.iotaDeg0 N (N * q') 1
          (dvd_mul_right N q') (one_dvd _)).range
          (ModularCurve.PDPairing.pushChar0 N (N * q') 1 ℤ
            (dvd_mul_right N q') (one_dvd _) φ) x := by
    show ModularCurve.PDPairing.coresAdd _ _ x = _
    rw [hB0]
  have hRHS : degeneracyTransfer₀Aux N q' ℤ (bezoutConjugator N q' a b hab)
      (bezoutConjugator_heckeUpper_dvd N q' a b hab) φ x
      = coresHom (heckeUpper N q')
          (pullbackHom ((iotaUpperEquiv N q').symm.toMonoidHom)
            (pullbackHom (alConjHom N q' (bezoutConjugator N q' a b hab)
              (bezoutConjugator_heckeUpper_dvd N q' a b hab)) φ)) x := rfl

  have hwash : coresHom (ModularCurve.PDPairing.iotaDeg0 N (N * q') 1
      (dvd_mul_right N q') (one_dvd _)).range
      (ModularCurve.PDPairing.pushChar0 N (N * q') 1 ℤ
        (dvd_mul_right N q') (one_dvd _) φ) x
      = coresHom (ModularCurve.PDPairing.iotaDeg0 N (N * q') 1
          (dvd_mul_right N q') (one_dvd _)).range
          (ModularCurve.PDPairing.pushChar0 N (N * q') 1 ℤ
            (dvd_mul_right N q') (one_dvd _) φ)
          (Additive.ofMul ((bezoutConjugator N q' a b hab)⁻¹ * Additive.toMul x *
            bezoutConjugator N q' a b hab)) := by
    rw [show Additive.ofMul ((bezoutConjugator N q' a b hab)⁻¹ * Additive.toMul x *
        bezoutConjugator N q' a b hab)
      = Additive.ofMul ((bezoutConjugator N q' a b hab)⁻¹ : Gamma0 N)
        + Additive.ofMul (Additive.toMul x)
        + Additive.ofMul (bezoutConjugator N q' a b hab : Gamma0 N) from rfl]
    rw [map_add, map_add, ofMul_inv, map_neg]
    have hx : Additive.ofMul (Additive.toMul x) = x := rfl
    rw [hx]
    abel

  have hG2 := Corestriction.coresHom_comp_apply (heckeUpper N q')
    (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom
    (Corestriction.surj_quotMap_of_surjective _ _ hσsurj)
    (pullbackHom ((iotaUpperEquiv N q').symm.toMonoidHom)
      (pullbackHom (alConjHom N q' (bezoutConjugator N q' a b hab)
        (bezoutConjugator_heckeUpper_dvd N q' a b hab)) φ))
    ((bezoutConjugator N q' a b hab)⁻¹ * Additive.toMul x * bezoutConjugator N q' a b hab)

  have hσg : (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom
      ((bezoutConjugator N q' a b hab)⁻¹ * Additive.toMul x * bezoutConjugator N q' a b hab)
      = Additive.toMul x := by
    show bezoutConjugator N q' a b hab *
        ((bezoutConjugator N q' a b hab)⁻¹ * Additive.toMul x * bezoutConjugator N q' a b hab) *
        (bezoutConjugator N q' a b hab)⁻¹ = Additive.toMul x
    group

  have hχ : ∀ (w : Gamma0 N)
      (h₁ : w ∈ (heckeUpper N q').comap
        (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom)
      (h₂ : w ∈ (ModularCurve.PDPairing.iotaDeg0 N (N * q') 1
        (dvd_mul_right N q') (one_dvd _)).range),
      ((pullbackHom ((iotaUpperEquiv N q').symm.toMonoidHom)
        (pullbackHom (alConjHom N q' (bezoutConjugator N q' a b hab)
          (bezoutConjugator_heckeUpper_dvd N q' a b hab)) φ)).comp
        (AddMonoidHom.mk' (fun j => Additive.ofMul
          (⟨(MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom
              (Additive.toMul j : ↥((heckeUpper N q').comap
                (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom)),
            (Additive.toMul j).2⟩ : ↥(heckeUpper N q')))
          (fun c d => by
            rw [← ofMul_mul]
            exact congrArg Additive.ofMul (Subtype.ext
              (map_mul (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom
                ((Additive.toMul c : ↥((heckeUpper N q').comap
                  (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom)) : Gamma0 N)
                ((Additive.toMul d : ↥((heckeUpper N q').comap
                  (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom)) : Gamma0 N))))))
        (Additive.ofMul ⟨w, h₁⟩)
      = (ModularCurve.PDPairing.pushChar0 N (N * q') 1 ℤ
          (dvd_mul_right N q') (one_dvd _) φ) (Additive.ofMul ⟨w, h₂⟩) := by
    intro w h₁ h₂
    have hwK : w ∈ (Ihara.ι₀ N q').range := by
      rw [← range_iotaDeg0_one N q']
      exact h₂
    obtain ⟨γ, hγ⟩ := hwK

    have hval : (⟨(MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom w,
        h₁⟩ : ↥(heckeUpper N q'))
        = iotaUpperHom N q' (alConjHom N q' (bezoutConjugator N q' a b hab)
            (bezoutConjugator_heckeUpper_dvd N q' a b hab) γ) := by
      refine Subtype.ext ?_
      rw [coe_iotaUpperHom, iota1_alConjHom]
      show bezoutConjugator N q' a b hab * w * (bezoutConjugator N q' a b hab)⁻¹
          = bezoutConjugator N q' a b hab * Ihara.ι₀ N q' γ *
            (bezoutConjugator N q' a b hab)⁻¹
      rw [hγ]
    have hsymmcollapse : ∀ z : Gamma0 (N * q'),
        (iotaUpperEquiv N q').symm.toMonoidHom (iotaUpperHom N q' z) = z := by
      intro z
      show (iotaUpperEquiv N q').symm (iotaUpperHom N q' z) = z
      rw [← iotaUpperEquiv_apply, MulEquiv.symm_apply_apply]

    have hL : ((pullbackHom ((iotaUpperEquiv N q').symm.toMonoidHom)
        (pullbackHom (alConjHom N q' (bezoutConjugator N q' a b hab)
          (bezoutConjugator_heckeUpper_dvd N q' a b hab)) φ)).comp
        (AddMonoidHom.mk' (fun j => Additive.ofMul
          (⟨(MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom
              (Additive.toMul j : ↥((heckeUpper N q').comap
                (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom)),
            (Additive.toMul j).2⟩ : ↥(heckeUpper N q')))
          (fun c d => by
            rw [← ofMul_mul]
            exact congrArg Additive.ofMul (Subtype.ext
              (map_mul (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom
                ((Additive.toMul c : ↥((heckeUpper N q').comap
                  (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom)) : Gamma0 N)
                ((Additive.toMul d : ↥((heckeUpper N q').comap
                  (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom)) : Gamma0 N))))))
        (Additive.ofMul ⟨w, h₁⟩)
        = φ (Additive.ofMul (alConjHom N q' (bezoutConjugator N q' a b hab)
            (bezoutConjugator_heckeUpper_dvd N q' a b hab)
            (alConjHom N q' (bezoutConjugator N q' a b hab)
              (bezoutConjugator_heckeUpper_dvd N q' a b hab) γ))) := by
      show (pullbackHom ((iotaUpperEquiv N q').symm.toMonoidHom)
          (pullbackHom (alConjHom N q' (bezoutConjugator N q' a b hab)
            (bezoutConjugator_heckeUpper_dvd N q' a b hab)) φ))
          (Additive.ofMul (⟨(MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom w,
            h₁⟩ : ↥(heckeUpper N q'))) = _
      rw [hval, pullbackHom_apply, hsymmcollapse, pullbackHom_apply]
    have hsq : φ (Additive.ofMul (alConjHom N q' (bezoutConjugator N q' a b hab)
        (bezoutConjugator_heckeUpper_dvd N q' a b hab)
        (alConjHom N q' (bezoutConjugator N q' a b hab)
          (bezoutConjugator_heckeUpper_dvd N q' a b hab) γ)))
        = φ (Additive.ofMul γ) := by
      rw [alConjHom_bezout_sq N q' a b hab]
      rw [show Additive.ofMul (alConjSqElt N q' a b hab * γ * (alConjSqElt N q' a b hab)⁻¹)
          = Additive.ofMul (alConjSqElt N q' a b hab) + Additive.ofMul γ
            + Additive.ofMul ((alConjSqElt N q' a b hab))⁻¹ from rfl]
      rw [map_add, map_add, ofMul_inv, map_neg]
      abel
    have hR : (ModularCurve.PDPairing.pushChar0 N (N * q') 1 ℤ
        (dvd_mul_right N q') (one_dvd _) φ) (Additive.ofMul ⟨w, h₂⟩)
        = φ (Additive.ofMul γ) := by
      have hj : (⟨w, h₂⟩ : ↥(ModularCurve.PDPairing.iotaDeg0 N (N * q') 1
          (dvd_mul_right N q') (one_dvd _)).range)
          = (ModularCurve.PDPairing.iotaDeg0 N (N * q') 1
              (dvd_mul_right N q') (one_dvd _)).ofInjective
              (ModularCurve.PDPairing.iotaDeg0_injective N (N * q') 1
                (dvd_mul_right N q') (one_dvd _)) γ := by
        refine Subtype.ext ?_
        rw [MonoidHom.ofInjective_apply]
        show w = ModularCurve.PDPairing.iotaDeg0 N (N * q') 1
          (dvd_mul_right N q') (one_dvd _) γ
        rw [iotaDeg0_one_eq_iota0, hγ]
      rw [hj]
      show φ (Additive.ofMul ((MonoidHom.ofInjective
        (ModularCurve.PDPairing.iotaDeg0_injective N (N * q') 1
          (dvd_mul_right N q') (one_dvd _))).symm
        ((MonoidHom.ofInjective (ModularCurve.PDPairing.iotaDeg0_injective N (N * q') 1
          (dvd_mul_right N q') (one_dvd _))) γ))) = _
      rw [MulEquiv.symm_apply_apply]
    rw [hL, hsq, hR]

  have hcongr := Corestriction.coresHom_congr hcomap.symm
    (ModularCurve.PDPairing.pushChar0 N (N * q') 1 ℤ
      (dvd_mul_right N q') (one_dvd _) φ)
    ((pullbackHom ((iotaUpperEquiv N q').symm.toMonoidHom)
      (pullbackHom (alConjHom N q' (bezoutConjugator N q' a b hab)
        (bezoutConjugator_heckeUpper_dvd N q' a b hab)) φ)).comp
      (AddMonoidHom.mk' (fun j => Additive.ofMul
        (⟨(MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom
            (Additive.toMul j : ↥((heckeUpper N q').comap
              (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom)),
          (Additive.toMul j).2⟩ : ↥(heckeUpper N q')))
        (fun c d => by
            rw [← ofMul_mul]
            exact congrArg Additive.ofMul (Subtype.ext
              (map_mul (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom
                ((Additive.toMul c : ↥((heckeUpper N q').comap
                  (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom)) : Gamma0 N)
                ((Additive.toMul d : ↥((heckeUpper N q').comap
                  (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom)) : Gamma0 N))))))
    (fun g hg => (hχ g (hcomap.symm ▸ hg) hg).symm)
    (Additive.ofMul ((bezoutConjugator N q' a b hab)⁻¹ * Additive.toMul x *
      bezoutConjugator N q' a b hab))
  refine hLHS.trans (hwash.trans (hcongr.trans (hG2.symm.trans ?_)))
  have harg : Additive.ofMul ((MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom
      ((bezoutConjugator N q' a b hab)⁻¹ * Additive.toMul x * bezoutConjugator N q' a b hab))
      = x := by
    rw [hσg]
    rfl
  rw [harg]
  exact hRHS.symm

private theorem jDeg0_one_eq_degeneracyTransfer₀ (hq' : q'.Prime) (hq'N : ¬ q' ∣ N)
    (φ : Additive (Gamma0 (N * q')) →+ ℤ) (x : Additive (Gamma0 N)) :
    ModularCurve.PDPairing.jDeg0 N (N * q') 1 ℤ ℤ (dvd_mul_right N q') (one_dvd _) φ x
      = degeneracyTransfer₀ N q' ℤ hq' hq'N φ x :=
  jDeg0_one_eq_degeneracyTransfer₀Aux N q'
    (Int.gcdA (q' : ℤ) (N : ℤ)) (-Int.gcdB (q' : ℤ) (N : ℤ))
    (bezout_of_prime_not_dvd N q' hq' hq'N) φ x

end Transfer0
p2m_reactivate "P2MW.S_LevelRaising_exists_parabolicPairings_perfect_mod_three.Corestriction"

end Transfer0Section
p2m_reactivate "P2MW.S_LevelRaising_exists_parabolicPairings_perfect_mod_three.Corestriction"

section Identifications
open scoped MatrixGroups

variable {N q' : ℕ}

private theorem q_dvd_mul_div (N q : ℕ) : q ∣ (N * q) / N := by
  rcases Nat.eq_zero_or_pos N with h | h
  · simp [h]
  · rw [Nat.mul_div_cancel_left q h]

private theorem iotaDeg0_one_eq_iota0 (N q : ℕ) (γ : Gamma0 (N * q)) :
    ModularCurve.PDPairing.iotaDeg0 N (N * q) 1 (dvd_mul_right N q) (one_dvd _) γ = Ihara.ι₀ N q γ := by
  refine Subtype.ext (Subtype.ext ?_)
  show (ModularCurve.PDPairing.conjLowerMat 1 ((γ : SL(2, ℤ)))
      (ModularCurve.PDPairing.dvd_entry0 N (N * q) 1 (dvd_mul_right N q) (one_dvd _) γ)
      : Matrix (Fin 2) (Fin 2) ℤ)
    = (((Ihara.ι₀ N q γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ModularCurve.PDPairing.conjLowerMat]

private theorem iotaDeg0_q_eq_iota1 (N q : ℕ) [NeZero q] (γ : Gamma0 (N * q)) :
    ModularCurve.PDPairing.iotaDeg0 N (N * q) q (dvd_mul_right N q) (q_dvd_mul_div N q) γ
      = Ihara.ι₁ N q γ :=
  Subtype.ext (Subtype.ext rfl)

private theorem iDeg0_one_eq_pullbackHom_iota0 (N q : ℕ) (A : Type*) [AddCommGroup A]
    (φ : Additive (Gamma0 N) →+ A) :
    ModularCurve.PDPairing.iDeg0 N (N * q) 1 ℤ A (dvd_mul_right N q) (one_dvd _) φ
      = pullbackHom (Ihara.ι₀ N q) φ := by
  refine AddMonoidHom.ext fun x => ?_
  show φ (Additive.ofMul (ModularCurve.PDPairing.iotaDeg0 N (N * q) 1 (dvd_mul_right N q) (one_dvd _)
      (Additive.toMul x)))
    = φ (Additive.ofMul (Ihara.ι₀ N q (Additive.toMul x)))
  rw [iotaDeg0_one_eq_iota0]

private theorem iDeg0_q_eq_pullbackHom_iota1 (N q : ℕ) (A : Type*) [AddCommGroup A] [NeZero q]
    (φ : Additive (Gamma0 N) →+ A) :
    ModularCurve.PDPairing.iDeg0 N (N * q) q ℤ A (dvd_mul_right N q) (q_dvd_mul_div N q) φ
      = pullbackHom (Ihara.ι₁ N q) φ := by
  refine AddMonoidHom.ext fun x => ?_
  show φ (Additive.ofMul (ModularCurve.PDPairing.iotaDeg0 N (N * q) q (dvd_mul_right N q) (q_dvd_mul_div N q)
      (Additive.toMul x)))
    = φ (Additive.ofMul (Ihara.ι₁ N q (Additive.toMul x)))
  rw [iotaDeg0_q_eq_iota1]

private theorem coresAdd_eq_coresHom {G : Type*} [Group G] (K : Subgroup G) [K.FiniteIndex]
    {A : Type*} [AddCommGroup A] (ψ : Additive ↥K →+ A) :
    ModularCurve.PDPairing.coresAdd K ψ = coresHom K ψ := by
  rw [HeckeEis.coresHom_eq_transfer]
  rfl

private theorem range_iotaDeg0_q (N q : ℕ) [NeZero q] :
    (ModularCurve.PDPairing.iotaDeg0 N (N * q) q (dvd_mul_right N q) (q_dvd_mul_div N q)).range
      = heckeUpper N q := by
  have h1 : (ModularCurve.PDPairing.iotaDeg0 N (N * q) q (dvd_mul_right N q) (q_dvd_mul_div N q)).range
      = (Ihara.ι₁ N q).range := by
    refine Subgroup.ext fun γ => ⟨?_, ?_⟩
    · rintro ⟨δ, rfl⟩
      exact ⟨δ, (iotaDeg0_q_eq_iota1 N q δ).symm⟩
    · rintro ⟨δ, rfl⟩
      exact ⟨δ, iotaDeg0_q_eq_iota1 N q δ⟩
  rw [h1, range_iota1 N (NeZero.ne q)]

private theorem jDeg0_q_eq_degeneracyTransfer₁_apply (N q : ℕ) [NeZero (N * q)] [NeZero q]
    (A : Type*) [AddCommGroup A]
    (ψ : Additive (Gamma0 (N * q)) →+ A) (x : Additive (Gamma0 N)) :
    ModularCurve.PDPairing.jDeg0 N (N * q) q ℤ A (dvd_mul_right N q) (q_dvd_mul_div N q) ψ x
      = degeneracyTransfer₁ N q A ψ x := by
  show ModularCurve.PDPairing.coresAdd _
      (ModularCurve.PDPairing.pushChar0 N (N * q) q A (dvd_mul_right N q) (q_dvd_mul_div N q) ψ) x
    = degeneracyTransfer₁ N q A ψ x
  rw [coresAdd_eq_coresHom]
  show _ = coresHom (heckeUpper N q)
      (pullbackHom ((iotaUpperEquiv N q).symm.toMonoidHom) ψ) x
  refine Corestriction.coresHom_congr (range_iotaDeg0_q N q) _ _ (fun g h₁ => ?_) x
  show ψ (Additive.ofMul (((ModularCurve.PDPairing.iotaDeg0 N (N * q) q (dvd_mul_right N q)
      (q_dvd_mul_div N q)).ofInjective (ModularCurve.PDPairing.iotaDeg0_injective N (N * q) q
      (dvd_mul_right N q) (q_dvd_mul_div N q))).symm ⟨g, h₁⟩))
    = ψ (Additive.ofMul ((iotaUpperEquiv N q).symm
        ⟨g, (range_iotaDeg0_q N q) ▸ h₁⟩))
  refine congrArg ψ (congrArg Additive.ofMul ?_)
  have e₁ : Ihara.ι₁ N q (((ModularCurve.PDPairing.iotaDeg0 N (N * q) q (dvd_mul_right N q)
      (q_dvd_mul_div N q)).ofInjective (ModularCurve.PDPairing.iotaDeg0_injective N (N * q) q
      (dvd_mul_right N q) (q_dvd_mul_div N q))).symm ⟨g, h₁⟩) = g := by
    have h := MulEquiv.apply_symm_apply ((ModularCurve.PDPairing.iotaDeg0 N (N * q) q (dvd_mul_right N q)
      (q_dvd_mul_div N q)).ofInjective (ModularCurve.PDPairing.iotaDeg0_injective N (N * q) q
      (dvd_mul_right N q) (q_dvd_mul_div N q))) ⟨g, h₁⟩
    have hval : ModularCurve.PDPairing.iotaDeg0 N (N * q) q (dvd_mul_right N q) (q_dvd_mul_div N q)
        (((ModularCurve.PDPairing.iotaDeg0 N (N * q) q (dvd_mul_right N q)
          (q_dvd_mul_div N q)).ofInjective (ModularCurve.PDPairing.iotaDeg0_injective N (N * q) q
          (dvd_mul_right N q) (q_dvd_mul_div N q))).symm ⟨g, h₁⟩) = g :=
      congrArg Subtype.val h
    rw [iotaDeg0_q_eq_iota1] at hval
    exact hval
  have e₂ : Ihara.ι₁ N q ((iotaUpperEquiv N q).symm
      ⟨g, (range_iotaDeg0_q N q) ▸ h₁⟩) = g :=
    congrArg Subtype.val ((iotaUpperEquiv N q).apply_symm_apply _)
  have hinj : Function.Injective (Ihara.ι₁ N q) := fun a b hab =>
    (iotaUpperEquiv N q).injective (Subtype.ext hab)
  exact hinj (e₁.trans e₂.symm)

private theorem gamma0HUpper_eq_heckeUpper (M ℓ : ℕ) :
    ModularCurve.PDPairing.Gamma0HUpper M ℓ = heckeUpper M ℓ := by
  refine Subgroup.ext fun γ => ?_
  rw [mem_heckeUpper]
  constructor
  · intro h
    exact ModularCurve.PDPairing.dvd_of_mem_Gamma0HUpper M ℓ ⟨γ, h⟩
  · intro h
    exact Subgroup.mem_subgroupOf.mpr (ModularCurve.PDPairing.mem_Gamma0Upper.mpr
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h))

private theorem heckeT0_eq_heckeOperatorHom_apply (M ℓ : ℕ) [NeZero ℓ] (A : Type*) [AddCommGroup A]
    (φ : Additive (Gamma0 M) →+ A) (x : Additive (Gamma0 M)) :
    ModularCurve.PDPairing.heckeT0 M ℓ A φ x = heckeOperatorHom M ℓ A φ x := by
  have hL : ModularCurve.PDPairing.heckeT0 M ℓ A φ x
      = coresHom (ModularCurve.PDPairing.Gamma0HUpper M ℓ)
          (φ.comp (MonoidHom.toAdditive (ModularCurve.PDPairing.conjL0 M ℓ))) x := by
    have hcores := HeckeEis.coresHom_eq_transfer (H := ModularCurve.PDPairing.Gamma0HUpper M ℓ)
      (φ.comp (MonoidHom.toAdditive (ModularCurve.PDPairing.conjL0 M ℓ)))
    rw [hcores]
    rfl
  rw [hL]
  show _ = coresHom (heckeUpper M ℓ) (pullbackHom (heckeConj M ℓ) φ) x
  refine Corestriction.coresHom_congr (gamma0HUpper_eq_heckeUpper M ℓ) _ _ (fun g h₁ => ?_) x
  exact congrArg φ (congrArg Additive.ofMul (Subtype.ext (Subtype.ext rfl)))

private theorem jDeg0_one_eq_degeneracyTransfer₀' (N q' : ℕ) [NeZero N] [NeZero q'] (hq' : q'.Prime) (hq'N : ¬ q' ∣ N)
    (φ : Additive (Gamma0 (N * q')) →+ ℤ) (x : Additive (Gamma0 N)) :
    haveI : NeZero (N * q') := ⟨Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne q')⟩
    ModularCurve.PDPairing.jDeg0 N (N * q') 1 ℤ ℤ (dvd_mul_right N q') (one_dvd _) φ x
      = degeneracyTransfer₀ N q' ℤ hq' hq'N φ x :=
  Transfer0.jDeg0_one_eq_degeneracyTransfer₀ N q' hq' hq'N φ x

end Identifications
p2m_reactivate "P2MW.S_LevelRaising_exists_parabolicPairings_perfect_mod_three.Corestriction"

private theorem descend {L L' K K' : Type} [AddCommGroup L] [Module ℤ L] [AddCommGroup L'] [Module ℤ L']
    [AddCommGroup K] [Module ℤ K] [AddCommGroup K'] [Module ℤ K']
    {c : ℤ} (hc : c ≠ 0) {B : L →ₗ[ℤ] L' →ₗ[ℤ] ℤ} {P : L →ₗ[ℤ] L' →ₗ[ℤ] ℤ} (hB : c • B = P)
    {B' : K →ₗ[ℤ] K' →ₗ[ℤ] ℤ} {P' : K →ₗ[ℤ] K' →ₗ[ℤ] ℤ} (hB' : c • B' = P')
    (x : L) (y : L') (z : K) (w : K') (h : P x y = P' z w) : B x y = B' z w := by
  apply mul_left_cancel₀ hc
  have e1 : P x y = c * B x y := by rw [← hB]; simp
  have e2 : P' z w = c * B' z w := by rw [← hB']; simp
  rw [← e1, ← e2]
  exact h

end ParabolicPairings
p2m_reactivate "P2MW.S_LevelRaising_exists_parabolicPairings_perfect_mod_three.Corestriction"

theorem solution
    (N q : ℕ) [NeZero N] [NeZero q] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (hTpar : ∀ (M ℓ : ℕ) [NeZero ℓ] (φ : Additive (Gamma0 M) →+ ℤ),
      ModularCurve.Period.IsParabolicHom (Gamma0 M) φ →
        ModularCurve.Period.IsParabolicHom (Gamma0 M) (HeckeEis.heckeOperatorHom M ℓ ℤ φ))
    (hrespar₀ : ∀ y ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ,
      HeckeEis.pullbackHom (Ihara.ι₀ N q) y ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q)) ℤ)
    (hrespar₁ : ∀ y ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ,
      HeckeEis.pullbackHom (Ihara.ι₁ N q) y ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q)) ℤ)
    (hβpar₀ : ∀ x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q)) ℤ,
      HeckeEis.degeneracyTransfer₀ N q ℤ hq hqN x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ)
    (hβpar₁ : ∀ x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q)) ℤ,
      HeckeEis.degeneracyTransfer₁ N q ℤ x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ) :
    ∃ (pair₁ : ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q)) ℤ →ₗ[ℤ]
        ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q)) ℤ →ₗ[ℤ] ℤ)
      (pair₀ : ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ →ₗ[ℤ]
        ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ →ₗ[ℤ] ℤ),
      ((∀ x, (∀ y, (3 : ℤ) ∣ pair₁ x y) → ∃ x', x = (3 : ℤ) • x') ∧
        (∀ y, (∀ x, (3 : ℤ) ∣ pair₁ x y) → ∃ y', y = (3 : ℤ) • y')) ∧
      ((∀ x, (∀ y, (3 : ℤ) ∣ pair₀ x y) → ∃ x', x = (3 : ℤ) • x') ∧
        (∀ y, (∀ x, (3 : ℤ) ∣ pair₀ x y) → ∃ y', y = (3 : ℤ) • y')) ∧
      (∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N * q →
        ∀ x y : ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q)) ℤ,
          pair₁ ⟨HeckeEis.heckeOperatorHom (N * q) ℓ ℤ x, hTpar (N * q) ℓ x x.2⟩ y =
            pair₁ x ⟨HeckeEis.heckeOperatorHom (N * q) ℓ ℤ y, hTpar (N * q) ℓ y y.2⟩) ∧
      (∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N * q →
        ∀ x y : ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ,
          pair₀ ⟨HeckeEis.heckeOperatorHom N ℓ ℤ x, hTpar N ℓ x x.2⟩ y =
            pair₀ x ⟨HeckeEis.heckeOperatorHom N ℓ ℤ y, hTpar N ℓ y y.2⟩) ∧
      (∀ (x : ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q)) ℤ)
        (y : ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ),
          pair₀ ⟨HeckeEis.degeneracyTransfer₀ N q ℤ hq hqN x, hβpar₀ x x.2⟩ y =
            pair₁ x ⟨HeckeEis.pullbackHom (Ihara.ι₀ N q) y, hrespar₀ y y.2⟩) ∧
      (∀ (x : ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q)) ℤ)
        (y : ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ),
          pair₀ ⟨HeckeEis.degeneracyTransfer₁ N q ℤ x, hβpar₁ x x.2⟩ y =
            pair₁ x ⟨HeckeEis.pullbackHom (Ihara.ι₁ N q) y, hrespar₁ y y.2⟩) := by
  haveI : IsFreeGroup ↥(Gamma 4) := ModularCurve.PDPairing.isFreeGroup_Gamma_four
  haveI hNq : NeZero (N * q) := ⟨Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne q)⟩
  obtain ⟨c, hc, hlev⟩ := ModularCurve.PDPairing.exists_forall_smul_eq_pairZ_and_perfect_mod_three
  obtain ⟨B₁, hB₁, hperf₁l, hperf₁r⟩ := hlev (N * q)
  obtain ⟨B₀, hB₀, hperf₀l, hperf₀r⟩ := hlev N
  have hT : ∀ (M ℓ : ℕ) [NeZero ℓ] (φ : Additive (Gamma0 M) →+ ℤ),
      heckeOperatorHom M ℓ ℤ φ = ModularCurve.PDPairing.heckeT0 M ℓ ℤ φ :=
    fun M ℓ _ φ => AddMonoidHom.ext fun g => (ParabolicPairings.heckeT0_eq_heckeOperatorHom_apply M ℓ ℤ φ g).symm
  refine ⟨B₁, B₀, ⟨hperf₁l, hperf₁r⟩, ⟨hperf₀l, hperf₀r⟩, ?_, ?_, ?_, ?_⟩
  · intro ℓ _ hℓ hℓNq x y
    refine ParabolicPairings.descend hc hB₁ hB₁ _ _ _ _ ?_
    show ModularCurve.PDPairing.pairZFun (N * q) (heckeOperatorHom (N * q) ℓ ℤ x) y
      = ModularCurve.PDPairing.pairZFun (N * q) x (heckeOperatorHom (N * q) ℓ ℤ y)
    rw [hT, hT]
    exact ModularCurve.PDPairing.pairZFun_heckeT0_comm (N * q) ℓ hℓ hℓNq x y x.2 y.2
  · intro ℓ _ hℓ hℓNq x y
    have hℓN : ¬ ℓ ∣ N := fun h => hℓNq (Dvd.dvd.mul_right h q)
    refine ParabolicPairings.descend hc hB₀ hB₀ _ _ _ _ ?_
    show ModularCurve.PDPairing.pairZFun N (heckeOperatorHom N ℓ ℤ x) y
      = ModularCurve.PDPairing.pairZFun N x (heckeOperatorHom N ℓ ℤ y)
    rw [hT, hT]
    exact ModularCurve.PDPairing.pairZFun_heckeT0_comm N ℓ hℓ hℓN x y x.2 y.2
  · intro x y
    refine ParabolicPairings.descend hc hB₀ hB₁ _ _ _ _ ?_
    show ModularCurve.PDPairing.pairZFun N (degeneracyTransfer₀ N q ℤ hq hqN x) y
      = ModularCurve.PDPairing.pairZFun (N * q) x (pullbackHom (Ihara.ι₀ N q) y)
    have hj : degeneracyTransfer₀ N q ℤ hq hqN (x : Additive (Gamma0 (N * q)) →+ ℤ)
        = ModularCurve.PDPairing.jDeg0 N (N * q) 1 ℤ ℤ (dvd_mul_right N q) (one_dvd _) x :=
      AddMonoidHom.ext fun g => (ParabolicPairings.jDeg0_one_eq_degeneracyTransfer₀' N q hq hqN x g).symm
    have hi : pullbackHom (Ihara.ι₀ N q) (y : Additive (Gamma0 N) →+ ℤ)
        = ModularCurve.PDPairing.iDeg0 N (N * q) 1 ℤ ℤ (dvd_mul_right N q) (one_dvd _) y :=
      (ParabolicPairings.iDeg0_one_eq_pullbackHom_iota0 N q ℤ y).symm
    rw [hj, hi]
    exact ModularCurve.PDPairing.pairZFun_jDeg0_iDeg0 N (N * q) 1 (dvd_mul_right N q) (one_dvd _) x y x.2 y.2
  · intro x y
    refine ParabolicPairings.descend hc hB₀ hB₁ _ _ _ _ ?_
    show ModularCurve.PDPairing.pairZFun N (degeneracyTransfer₁ N q ℤ x) y
      = ModularCurve.PDPairing.pairZFun (N * q) x (pullbackHom (Ihara.ι₁ N q) y)
    have hj : degeneracyTransfer₁ N q ℤ (x : Additive (Gamma0 (N * q)) →+ ℤ)
        = ModularCurve.PDPairing.jDeg0 N (N * q) q ℤ ℤ (dvd_mul_right N q) (ParabolicPairings.q_dvd_mul_div N q) x :=
      AddMonoidHom.ext fun g => (ParabolicPairings.jDeg0_q_eq_degeneracyTransfer₁_apply N q ℤ x g).symm
    have hi : pullbackHom (Ihara.ι₁ N q) (y : Additive (Gamma0 N) →+ ℤ)
        = ModularCurve.PDPairing.iDeg0 N (N * q) q ℤ ℤ (dvd_mul_right N q) (ParabolicPairings.q_dvd_mul_div N q) y :=
      (ParabolicPairings.iDeg0_q_eq_pullbackHom_iota1 N q ℤ y).symm
    rw [hj, hi]
    exact ModularCurve.PDPairing.pairZFun_jDeg0_iDeg0 N (N * q) q (dvd_mul_right N q) (ParabolicPairings.q_dvd_mul_div N q) x y
      x.2 y.2

end S_LevelRaising_exists_parabolicPairings_perfect_mod_three
end P2MW
export P2MW.S_LevelRaising_exists_parabolicPairings_perfect_mod_three (solution)
