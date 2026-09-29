-- Prove2me | solution 1 for ModularCurve.algebra_isIntegral_integralClosure_adjoin_jGeomGen_of_exists_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/7308bd4d-5537-5f4a-9622-f36031cecfc2

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Theorems.Thm_ModularCurve_NodeLocalized_isDiscreteValuationRing_coeffSubring
import Theorems.Thm_ModularCurve_NodeLocalized_finite_residueField_coeffSubring
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_algebra_isIntegral_integralClosure_adjoin_jGeomGen_of_exists_apply_eq
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false
set_option linter.unusedVariables false

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_algebra_isIntegral_integralClosure_adjoin_jGeomGen_of_exists_apply_eq.AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_algebra_isIntegral_integralClosure_adjoin_jGeomGen_of_exists_apply_eq.ModularCurve"
p2m_open "ModularCurve.NodeLocalized P2MW.S_ModularCurve_algebra_isIntegral_integralClosure_adjoin_jGeomGen_of_exists_apply_eq.ModularCurve.NodeLocalized"

section
open scoped IntermediateField.algebraAdjoinAdjoin
open IntermediateField Polynomial
namespace AlgebraicCurve
p2m_open "AlgebraicCurve"
variable {K F : Type*} [Field K] [Field F] [Algebra K F] {j : F}
theorem algebraMap_mem_integralClosure_adjoin (c : K) :
    algebraMap K F c ∈ integralClosure (Algebra.adjoin K ({j} : Set F)) F := by
  rw [mem_integralClosure_iff, IsScalarTower.algebraMap_apply K (Algebra.adjoin K ({j} : Set F)) F]
  exact isIntegral_algebraMap

theorem self_mem_integralClosure_adjoin :
    j ∈ integralClosure (Algebra.adjoin K ({j} : Set F)) F := by
  rw [mem_integralClosure_iff]
  have : j = algebraMap (Algebra.adjoin K ({j} : Set F)) F ⟨j, Algebra.self_mem_adjoin_singleton K
      j⟩ :=
    rfl
  rw [this]
  exact isIntegral_algebraMap
end AlgebraicCurve
end

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldC jGeomGen NodeLocalized.redRestrict"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "coeffSubring redRestrict isDiscreteValuationRing_coeffSubring finite_residueField_coeffSubring"
p2m_open "ModularCurve.NodeLocalized ModularCurve"

section ResidueAlgebraic

theorem c4_exists_monic_of_mem_finite_subring {k : Type*} [CommRing k] (k₀ T : Subring k) (hle : k₀ ≤ T) [Finite ↥T]
    (c : k) (hc : c ∈ T) : ∃ P : Polynomial k, P.Monic ∧ P.eval c = 0 ∧ ∀ i, P.coeff i ∈ k₀ := by
  letI : Algebra ↥k₀ ↥T := (Subring.inclusion hle).toAlgebra
  haveI : Module.Finite ↥k₀ ↥T := Module.Finite.of_finite
  haveI : Algebra.IsIntegral ↥k₀ ↥T := Algebra.IsIntegral.of_finite ↥k₀ ↥T
  obtain ⟨P₀, hP₀, hP₀a⟩ : IsIntegral ↥k₀ (⟨c, hc⟩ : ↥T) := Algebra.IsIntegral.isIntegral _
  refine ⟨P₀.map k₀.subtype, hP₀.map _, ?_, fun i => ?_⟩
  · have h := congrArg (Subtype.val : ↥T → k) hP₀a
    have h2 := Polynomial.hom_eval₂ P₀ (algebraMap ↥k₀ ↥T) T.subtype ⟨c, hc⟩
    rw [Polynomial.eval_map]
    exact h2.symm.trans h
  · rw [Polynomial.coeff_map]
    exact (P₀.coeff i).2

variable {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]

theorem c4_redRestrict_eq_zero_of_not_isUnit (red : A →+* k) (hred : Function.Surjective red)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (x : ↥(coeffSubring A K)) (hx : ¬ IsUnit x) : redRestrict red K x = 0 := by
  by_contra h
  apply hx
  have hxA : IsUnit (⟨(x : AlgebraicClosure ℚ), x.2.1⟩ : A) := by
    by_contra hnu
    apply h
    have hm : (⟨(x : AlgebraicClosure ℚ), x.2.1⟩ : A) ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have hker : RingHom.ker red = IsLocalRing.maximalIdeal A :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective red hred)
    rw [← hker] at hm
    exact hm
  obtain ⟨u, hu⟩ := hxA
  have hmul : (x : AlgebraicClosure ℚ) * (((u⁻¹ : Aˣ) : A) : AlgebraicClosure ℚ) = 1 := by
    have h1 : (((u : A) * ((u⁻¹ : Aˣ) : A) : A) : AlgebraicClosure ℚ) = ((1 : A) : AlgebraicClosure ℚ) :=
      congrArg Subtype.val u.mul_inv
    rw [hu] at h1
    exact h1
  have hy : (((u⁻¹ : Aˣ) : A) : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ)⁻¹ := eq_inv_of_mul_eq_one_right hmul
  have hyK : (((u⁻¹ : Aˣ) : A) : AlgebraicClosure ℚ) ∈ K := by
    rw [hy]
    exact K.inv_mem x.2.2
  exact IsUnit.of_mul_eq_one (⟨_, ((u⁻¹ : Aˣ) : A).2, hyK⟩ : ↥(coeffSubring A K)) (Subtype.ext hmul)

theorem c4_finite_range_redRestrict (q : ℕ) [Fact q.Prime] [CharP k q] (red : A →+* k) (hred : Function.Surjective red)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] : Finite ↥(redRestrict red K).range := by
  have hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A := fun c => by
    rw [← RingHom.mem_ker, IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective red hred)]
  haveI hDVR : IsDiscreteValuationRing ↥(coeffSubring A K) := isDiscreteValuationRing_coeffSubring (q := q) red hker K
  have hq : ((q : ℕ) : A) ∈ IsLocalRing.maximalIdeal A := (hker _).mp (by rw [map_natCast, CharP.cast_eq_zero])
  haveI hfin : Finite (IsLocalRing.ResidueField ↥(coeffSubring A K)) := finite_residueField_coeffSubring hq K
  haveI : IsLocalHom (redRestrict red K) := ⟨fun x hx => by
    by_contra hnu
    exact hx.ne_zero (c4_redRestrict_eq_zero_of_not_isUnit red hred K x hnu)⟩
  let ρbar : IsLocalRing.ResidueField ↥(coeffSubring A K) →+* k := IsLocalRing.ResidueField.lift (redRestrict red K)
  have hsub : Set.range (redRestrict red K) ⊆ Set.range ρbar := by
    rintro _ ⟨x, rfl⟩
    exact ⟨IsLocalRing.residue _ x, rfl⟩
  have hs : ((redRestrict red K).range : Set k).Finite := by
    rw [RingHom.coe_range]
    exact (Set.finite_range ρbar).subset hsub
  exact hs.to_subtype

theorem c4_exists_monic_coeff_mem_range_redRestrict (q : ℕ) [Fact q.Prime] [CharP k q] (red : A →+* k)
    (hred : Function.Surjective red) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] (c : k) :
    ∃ P : Polynomial k, P.Monic ∧ P.eval c = 0 ∧ ∀ i, P.coeff i ∈ (redRestrict red K).range := by
  obtain ⟨a, rfl⟩ := hred c
  have halg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.isAlgebraic ℚ <;>
      first | with_reducible_and_instances rfl | exact Subsingleton.elim _ _
  haveI : FiniteDimensional ℚ ↥(IntermediateField.adjoin ℚ {(a : AlgebraicClosure ℚ)}) :=
    IntermediateField.adjoin.finiteDimensional (halg.isAlgebraic _).isIntegral
  haveI : FiniteDimensional ℚ ↥(K ⊔ IntermediateField.adjoin ℚ {(a : AlgebraicClosure ℚ)}) :=
    IntermediateField.finiteDimensional_sup _ _
  haveI := c4_finite_range_redRestrict q red hred (K ⊔ IntermediateField.adjoin ℚ {(a : AlgebraicClosure ℚ)})
  refine c4_exists_monic_of_mem_finite_subring (redRestrict red K).range
    (redRestrict red (K ⊔ IntermediateField.adjoin ℚ {(a : AlgebraicClosure ℚ)})).range ?_ (red a) ?_
  · rintro _ ⟨x, rfl⟩
    exact ⟨⟨(x : AlgebraicClosure ℚ), x.2.1, (le_sup_left : K ≤ _) x.2.2⟩, rfl⟩
  · exact ⟨⟨(a : AlgebraicClosure ℚ), a.2, (le_sup_right : IntermediateField.adjoin ℚ {(a : AlgebraicClosure ℚ)} ≤ _)
      (IntermediateField.mem_adjoin_simple_self ℚ _)⟩, rfl⟩

end ResidueAlgebraic

end ModularCurve.NodeLocalized

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) (hred : Function.Surjective red)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    {C : Type*} [CommRing C]
    (g : C →+* ↥((integralClosure ↥(Algebra.adjoin k ({jGeomGen k N} : Set ↥(modularFunctionFieldC k N))) ↥(modularFunctionFieldC k N)).toSubring))
    (hconst : ∀ a : ↥(coeffSubring A K), ∃ c, ((g c : ↥((integralClosure ↥(Algebra.adjoin k ({jGeomGen k N} : Set ↥(modularFunctionFieldC k N))) ↥(modularFunctionFieldC k N)).toSubring)) : ↥(modularFunctionFieldC k N))
      = algebraMap k ↥(modularFunctionFieldC k N) (NodeLocalized.redRestrict red K a))
    (hj : ∃ c, ∃ n : ℕ, 0 < n ∧ ((g c : ↥((integralClosure ↥(Algebra.adjoin k ({jGeomGen k N} : Set ↥(modularFunctionFieldC k N))) ↥(modularFunctionFieldC k N)).toSubring)) : ↥(modularFunctionFieldC k N)) = jGeomGen k N ^ n) :
    @Algebra.IsIntegral C ↥((integralClosure ↥(Algebra.adjoin k ({jGeomGen k N} : Set ↥(modularFunctionFieldC k N))) ↥(modularFunctionFieldC k N)).toSubring) _ _ g.toAlgebra := by
  letI := g.toAlgebra
  let D : Subring (modularFunctionFieldC k N) :=
    (integralClosure ↥(Algebra.adjoin k ({jGeomGen k N} : Set ↥(modularFunctionFieldC k N))) ↥(modularFunctionFieldC k N)).toSubring
  let T := integralClosure C ↥D
  let val : ↥D →+* modularFunctionFieldC k N := D.subtype
  have hvalinj : Function.Injective val := Subtype.val_injective
  let φ : C →+* modularFunctionFieldC k N := val.comp g

  have hT_const : ∀ c : k, (⟨algebraMap k (modularFunctionFieldC k N) c, AlgebraicCurve.algebraMap_mem_integralClosure_adjoin c⟩ : ↥D) ∈ T := by
    intro c
    obtain ⟨Pk, hPk, hPkc, hcoef⟩ := ModularCurve.NodeLocalized.c4_exists_monic_coeff_mem_range_redRestrict q red hred K c
    rw [mem_integralClosure_iff]
    have hlift : Pk.map (algebraMap k (modularFunctionFieldC k N)) ∈ Polynomial.lifts φ := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro i
      rw [Polynomial.coeff_map]
      obtain ⟨a, ha⟩ := hcoef i
      obtain ⟨c', hc'⟩ := hconst a
      exact ⟨c', by rw [← ha, ← hc']; rfl⟩
    obtain ⟨Q, hQ, -, hQm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift (hPk.map _)
    refine ⟨Q, hQm, ?_⟩
    apply hvalinj
    rw [Polynomial.hom_eval₂, map_zero]
    show Polynomial.eval₂ φ (algebraMap k (modularFunctionFieldC k N) c) Q = 0
    rw [← Polynomial.eval_map, hQ, Polynomial.eval_map, Polynomial.eval₂_at_apply, hPkc, map_zero]

  have hT_j : (⟨jGeomGen k N, AlgebraicCurve.self_mem_integralClosure_adjoin⟩ : ↥D) ∈ T := by
    obtain ⟨c, n, hn, hc⟩ := hj
    rw [mem_integralClosure_iff]
    refine ⟨Polynomial.X ^ n - Polynomial.C c, Polynomial.monic_X_pow_sub_C c hn.ne', ?_⟩
    apply hvalinj
    rw [Polynomial.hom_eval₂, map_zero, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, sub_eq_zero]
    exact hc.symm

  have hB : ∀ x ∈ Algebra.adjoin k ({jGeomGen k N} : Set (modularFunctionFieldC k N)), ∃ hx : x ∈ D, (⟨x, hx⟩ : ↥D) ∈ T := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact ⟨_, hT_j⟩
    | algebraMap c => exact ⟨_, hT_const c⟩
    | add x y _ _ ihx ihy =>
        obtain ⟨hx, hx'⟩ := ihx
        obtain ⟨hy, hy'⟩ := ihy
        refine ⟨D.add_mem hx hy, ?_⟩
        have e : (⟨x + y, D.add_mem hx hy⟩ : ↥D) = ⟨x, hx⟩ + ⟨y, hy⟩ := Subtype.ext rfl
        rw [e]
        exact T.add_mem hx' hy'
    | mul x y _ _ ihx ihy =>
        obtain ⟨hx, hx'⟩ := ihx
        obtain ⟨hy, hy'⟩ := ihy
        refine ⟨D.mul_mem hx hy, ?_⟩
        have e : (⟨x * y, D.mul_mem hx hy⟩ : ↥D) = ⟨x, hx⟩ * ⟨y, hy⟩ := Subtype.ext rfl
        rw [e]
        exact T.mul_mem hx' hy'
  let ψ : ↥(Algebra.adjoin k ({jGeomGen k N} : Set (modularFunctionFieldC k N))) →+* ↥(integralClosure C ↥D) :=
    { toFun := fun b => ⟨⟨(b : modularFunctionFieldC k N), (hB b b.2).1⟩, (hB b b.2).2⟩
      map_one' := Subtype.ext (Subtype.ext rfl)
      map_mul' := fun _ _ => Subtype.ext (Subtype.ext rfl)
      map_zero' := Subtype.ext (Subtype.ext rfl)
      map_add' := fun _ _ => Subtype.ext (Subtype.ext rfl) }

  refine ⟨fun r => ?_⟩
  obtain ⟨p, hp, hpr⟩ : IsIntegral ↥(Algebra.adjoin k ({jGeomGen k N} : Set (modularFunctionFieldC k N)))
    (r : modularFunctionFieldC k N) := r.2
  have hint : IsIntegral ↥(integralClosure C ↥D) r := by
    refine ⟨p.map ψ, hp.map ψ, ?_⟩
    apply hvalinj
    rw [Polynomial.eval₂_map, Polynomial.hom_eval₂, map_zero]
    exact hpr
  exact isIntegral_trans r hint

end

end S_ModularCurve_algebra_isIntegral_integralClosure_adjoin_jGeomGen_of_exists_apply_eq
end P2MW
export P2MW.S_ModularCurve_algebra_isIntegral_integralClosure_adjoin_jGeomGen_of_exists_apply_eq (solution)
