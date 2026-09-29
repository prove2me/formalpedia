-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.reducesToOne_of_inertia_cyclotomic_of_mem_finPts
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/f937d536-afc6-5ed3-8657-682b8c247d17

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Theorems.Thm_HopfAlgebra_exists_surjective_bialgHom_monoidAlgebra_of_inertiaCyclotomic_submonoid
import Theorems.Thm_PDivisibleGroup_finite_point_and_natCard_point_eq_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_reducesToOne_of_inertia_cyclotomic_of_mem_finPts
p2m_attr_erase "instance" "MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra"
p2m_attr_erase "simp" "CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply"

set_option autoImplicit false

open scoped MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve ModularCurve.XHDRLevel AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (M : ℕ) [NeZero M] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)
    (hrep : Nonempty (RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))))

    (R : Type) [CommRing R] [IsDomain R] [HenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)]
    [Algebra R (AlgebraicClosure ℚ)] [FaithfulSMul R (AlgebraicClosure ℚ)]
    (hRA : ∀ x : R, algebraMap R (AlgebraicClosure ℚ) x ∈ Pl)
    (hRdvr : IsDiscreteValuationRing R) (hRirr : Irreducible ((p : ℕ) : R))
    (hRfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ Pl.inertiaSubgroupIn ℚ ↔ ∀ x : R, σ (algebraMap R (AlgebraicClosure ℚ) x) = algebraMap R (AlgebraicClosure ℚ) x)
    (hRmax : ∀ y ∈ Pl, (∀ σ ∈ Pl.inertiaSubgroupIn ℚ, σ y = y) → ∃ x : R, algebraMap R (AlgebraicClosure ℚ) x = y)

    {h : ℕ} (𝒢 : PDivisibleGroup R p h)
    (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ ModularCurve.JH M H)
    (hΔinj : Function.Injective Δ)
    (hΔlev : ∀ (v : ℕ) (y : ModularCurve.JH M H), y ∈ O.finPts (p ^ v) ↔
      ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y)
    (hΔgal : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[R] AlgebraicClosure ℚ),
      (∀ x : AlgebraicClosure ℚ, τ' x = τ x) →
      ∀ z : 𝒢.Points (AlgebraicClosure ℚ), Δ (τ' • z) = τ • Δ z) :
    ∀ x : ModularCurve.JH M H, x ∈ O.finPts p →
      (∀ σ ∈ Pl.inertiaSubgroupIn ℚ, ∀ c : ℕ,
          (∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ ^ c) → σ • x = c • x) →
      ∃ y : 𝒢.Point (AlgebraicClosure ℚ) 1,
        Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) 1 (Additive.ofMul y)) = x ∧
        ∀ a : 𝒢.level 1, Pl.valuation (PDivisibleGroup.Point.toAlgHom y a -
          algebraMap R (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1 := by
  classical
  have hp : p.Prime := Fact.out
  intro x hx hcyc
  obtain ⟨y, hy⟩ := (hΔlev 1 x).1 (by rwa [pow_one])
  refine ⟨y, hy, ?_⟩

  let Φ : 𝒢.Point (AlgebraicClosure ℚ) 1 → ModularCurve.JH M H := fun f =>
    Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) 1 (Additive.ofMul f))
  have hΦmul : ∀ f g, Φ (f * g) = Φ f + Φ g := fun f g => by
    simp only [Φ, ofMul_mul, map_add]
  have hΦone : Φ 1 = 0 := by simp only [Φ, ofMul_one, map_zero]
  have hΦpow : ∀ (f) (n : ℕ), Φ (f ^ n) = n • Φ f := fun f n => by
    simp only [Φ, ofMul_pow, map_nsmul]
  have hΦinv : ∀ f, Φ f⁻¹ = -Φ f := fun f => by
    simp only [Φ, ofMul_inv, map_neg]
  have hΦinj : Function.Injective Φ := fun f g hfg =>
    Additive.ofMul.injective (PDivisibleGroup.pointsMkAdd_injective 𝒢 1 (hΔinj hfg))

  have hτ' : ∀ σ ∈ Pl.inertiaSubgroupIn ℚ, ∃ τ' : AlgebraicClosure ℚ ≃ₐ[R] AlgebraicClosure ℚ, ∀ z, τ' z = σ z :=
    fun σ hσ => ⟨{ σ.toRingEquiv with commutes' := fun r => (hRfix σ).1 hσ r }, fun _ => rfl⟩
  have hΦσ : ∀ σ ∈ Pl.inertiaSubgroupIn ℚ, ∀ (τ' : AlgebraicClosure ℚ ≃ₐ[R] AlgebraicClosure ℚ), (∀ z, τ' z = σ z) →
      ∀ f, Φ (𝒢.pointMap (τ' : AlgebraicClosure ℚ →ₐ[R] AlgebraicClosure ℚ) 1 f) = σ • Φ f := by
    intro σ hσ τ' hτ f
    simp only [Φ]
    rw [← PDivisibleGroup.Points.smul_pointsMkAdd, hΔgal σ τ' hτ]

  let Dg : Subgroup (𝒢.Point (AlgebraicClosure ℚ) 1) :=
    { carrier := {f | ∀ σ ∈ Pl.inertiaSubgroupIn ℚ, ∀ c : ℕ,
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ ^ c) → σ • Φ f = c • Φ f}
      mul_mem' := fun {f g} hf hg σ hσ c hc => by
        change σ • Φ (f * g) = c • Φ (f * g)
        rw [hΦmul, smul_add σ (Φ f) (Φ g), smul_add c (Φ f) (Φ g), hf σ hσ c hc, hg σ hσ c hc]
      one_mem' := fun σ hσ c hc => by
        change σ • Φ 1 = c • Φ 1
        rw [hΦone]
        have h0 : σ • (0 : ModularCurve.JH M H) = 0 := by
          have h00 := smul_add σ (0 : ModularCurve.JH M H) 0
          rw [add_zero] at h00
          exact (add_left_cancel (a := σ • (0 : ModularCurve.JH M H)) (h00.symm.trans (add_zero _).symm))
        rw [h0, smul_zero]
      inv_mem' := fun {f} hf σ hσ c hc => by
        change σ • Φ f⁻¹ = c • Φ f⁻¹
        rw [hΦinv, smul_neg σ (Φ f), smul_neg c (Φ f), hf σ hσ c hc] }
  have hyD : y ∈ Dg := fun σ hσ c hc => by
    change σ • Φ y = c • Φ y
    simp only [Φ]
    rw [hy]
    exact hcyc σ hσ c hc

  haveI : Finite (𝒢.Point (AlgebraicClosure ℚ) 1) := (PDivisibleGroup.finite_point_and_natCard_point_eq_pow p 𝒢 (AlgebraicClosure ℚ) 1).1
  obtain ⟨a, -, ha⟩ : ∃ a ≤ 1 * h, Nat.card ↥Dg = p ^ a := by
    rw [← Nat.dvd_prime_pow hp, ← (PDivisibleGroup.finite_point_and_natCard_point_eq_pow p 𝒢 (AlgebraicClosure ℚ) 1).2]
    exact Subgroup.card_subgroup_dvd_card Dg

  have hD : ∀ σ ∈ Pl.inertiaSubgroupIn ℚ, ∀ c : ℕ,
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ ^ c) →
      ∀ f : WithConv (𝒢.level 1 →ₐ[R] AlgebraicClosure ℚ), f ∈ Dg.toSubmonoid →
        ∀ g : WithConv (𝒢.level 1 →ₐ[R] AlgebraicClosure ℚ), (∀ b : 𝒢.level 1, g b = σ (f b)) → g = f ^ c := by
    intro σ hσ c hc f hf g hg
    obtain ⟨τ', hτ⟩ := hτ' σ hσ
    have hgf : (PDivisibleGroup.Point.ofConv g : 𝒢.Point (AlgebraicClosure ℚ) 1) =
        𝒢.pointMap (τ' : AlgebraicClosure ℚ →ₐ[R] AlgebraicClosure ℚ) 1 (PDivisibleGroup.Point.ofConv f) :=
      PDivisibleGroup.Point.ext fun b => (hg b).trans (hτ _).symm
    apply hΦinj
    change Φ (PDivisibleGroup.Point.ofConv g) = Φ ((PDivisibleGroup.Point.ofConv f) ^ c)
    rw [hΦpow, hgf, hΦσ σ hσ τ' hτ]
    exact hf σ hσ c hc

  obtain ⟨p₀, -, hp₀⟩ :=
    HopfAlgebra.exists_surjective_bialgHom_monoidAlgebra_of_inertiaCyclotomic_submonoid p hp2 Pl R hRA hRdvr hRirr
      hRfix hRmax (𝒢.level 1) (Dg.toSubmonoid : Submonoid (WithConv (𝒢.level 1 →ₐ[R] AlgebraicClosure ℚ))) a ha hD
  obtain ⟨g, hg⟩ := (hp₀ (PDivisibleGroup.Point.toAlgHom y)).2 hyD

  have hroot : ∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → Pl.valuation (ζ - 1) < 1 := by
    intro ζ hζ
    have hζmem : ζ ∈ Pl := by
      rw [← ValuationSubring.valuation_le_one_iff]
      by_contra hlt
      push Not at hlt
      have := one_lt_pow₀ hlt hp.ne_zero
      rw [← map_pow, hζ, map_one] at this
      exact lt_irrefl _ this
    let z : ↥Pl := ⟨ζ, hζmem⟩
    have hz : z ^ p = 1 := Subtype.ext hζ
    have hz1 : z - 1 ∈ IsLocalRing.maximalIdeal ↥Pl := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_one]
      have h1 : (IsLocalRing.residue ↥Pl z - 1) ^ p = 0 := by
        rw [sub_pow_char, ← map_pow, hz, map_one, one_pow, sub_self]
      exact (pow_eq_zero_iff hp.ne_zero).1 h1
    exact (ValuationSubring.valuation_lt_one_iff Pl (z - 1)).1 hz1

  have hval : ∀ b : MonoidAlgebra R (Multiplicative (Fin a → ZMod p)),
      Pl.valuation (g b - algebraMap R (AlgebraicClosure ℚ) (Coalgebra.counit (R := R) b)) < 1 := by
    intro b
    induction b using MonoidAlgebra.induction_on with
    | of γ =>
      have hγp : γ ^ p = 1 := by
        have h0 : p • (Multiplicative.toAdd γ) = 0 := by
          funext i
          simp
        rw [show γ ^ p = Multiplicative.ofAdd (p • Multiplicative.toAdd γ) from rfl, h0]
        rfl
      rw [MonoidAlgebra.of_apply, MonoidAlgebra.counit_single, CommSemiring.counit_apply, map_one]
      apply hroot
      rw [← map_pow, MonoidAlgebra.single_pow, one_pow, hγp, ← MonoidAlgebra.one_def, map_one]
    | add u v hu hv =>
      rw [map_add, map_add, map_add, add_sub_add_comm]
      exact Valuation.map_add_lt _ hu hv
    | smul r u hu =>
      have e1 : g (r • u) = algebraMap R (AlgebraicClosure ℚ) r * g u := by rw [map_smul, Algebra.smul_def]
      have e2 : algebraMap R (AlgebraicClosure ℚ) (Coalgebra.counit (R := R) (r • u)) =
          algebraMap R (AlgebraicClosure ℚ) r * algebraMap R (AlgebraicClosure ℚ) (Coalgebra.counit (R := R) u) := by
        rw [map_smul, smul_eq_mul, RingHom.map_mul]
      rw [e1, e2, ← mul_sub, map_mul]
      calc Pl.valuation (algebraMap R (AlgebraicClosure ℚ) r) *
            Pl.valuation (g u - algebraMap R (AlgebraicClosure ℚ) (Coalgebra.counit (R := R) u))
          ≤ 1 * Pl.valuation (g u - algebraMap R (AlgebraicClosure ℚ) (Coalgebra.counit (R := R) u)) :=
            mul_le_mul_left ((ValuationSubring.valuation_le_one_iff Pl _).2 (hRA r)) _
        _ < 1 := by rw [one_mul]; exact hu

  intro a₀
  have hya : PDivisibleGroup.Point.toAlgHom y a₀ = g (p₀ a₀) := by
    rw [← hg]
    rfl
  rw [hya, ← CoalgHomClass.counit_comp_apply p₀ a₀]
  exact hval (p₀ a₀)

end S_ModularCurve_JHNeronObjectAtP_reducesToOne_of_inertia_cyclotomic_of_mem_finPts
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_reducesToOne_of_inertia_cyclotomic_of_mem_finPts (solution)
