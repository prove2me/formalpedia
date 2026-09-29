-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.card_le_finrank_quotient_of_forall_ker_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/877cc559-b1ff-51f2-93a9-9dd73b928e26

import Mathlib
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_ValuationSubring_exists_valuation_pow_lt_of_isAlgebraic
import Theorems.Thm_Valued_isAdicComplete_integer_span_singleton_of_forall_exists_pow_lt
import Theorems.Thm_AdicCompletion_exists_ringHom_comp_algebraMap_eq_of_forall_exists_pow_le_comap
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_valuation_coe_lt_one_of_maximalIdeal_eq_span
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_card_le_finrank_quotient_of_forall_ker_eq
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

universe u

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_card_le_finrank_quotient_of_forall_ker_eq.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_card_le_finrank_quotient_of_forall_ker_eq.ModularCurve.PlaceSpecialization"

section Generic
set_option maxHeartbeats 1600000
p2m_open "AdicCompletion P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_card_le_finrank_quotient_of_forall_ker_eq.AdicCompletion Valued"

namespace AdicCompletion
p2m_export "AdicCompletion" "map eval mk eval_of of module mk_surjective map_zero ext algebraMap_apply pow_smul_top_eq_ker_eval of_surjective exists_ringHom_comp_algebraMap_eq_of_forall_exists_pow_le_comap"
namespace ValuedLift
p2m_open "AdicCompletion"

theorem ringHom_ext_of_comp_algebraMap_eq {B : Type*} [CommRing B] (𝔪 : Ideal B) (h𝔪 : 𝔪.FG)
    {S : Type*} [CommRing S] (J : Ideal S) [IsHausdorff J S]
    (χ₁ χ₂ : AdicCompletion 𝔪 B →+* S)
    (hagree : χ₁.comp (algebraMap B (AdicCompletion 𝔪 B)) = χ₂.comp (algebraMap B (AdicCompletion 𝔪 B)))
    (h₁ : ∀ k : ℕ, ∃ n : ℕ, ∀ x ∈ (𝔪 ^ n • ⊤ : Submodule B (AdicCompletion 𝔪 B)), χ₁ x ∈ J ^ k)
    (h₂ : ∀ k : ℕ, ∃ n : ℕ, ∀ x ∈ (𝔪 ^ n • ⊤ : Submodule B (AdicCompletion 𝔪 B)), χ₂ x ∈ J ^ k) :
    χ₁ = χ₂ := by
  apply RingHom.ext
  intro x
  apply eq_of_sub_eq_zero
  apply IsHausdorff.haus (‹IsHausdorff J S›)
  intro k
  obtain ⟨n₁, hn₁⟩ := h₁ k
  obtain ⟨n₂, hn₂⟩ := h₂ k
  set n := max n₁ n₂ with hn

  obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (eval 𝔪 B n x)
  have hker : x - algebraMap B (AdicCompletion 𝔪 B) b ∈ (𝔪 ^ n • ⊤ : Submodule B (AdicCompletion 𝔪 B)) := by
    rw [pow_smul_top_eq_ker_eval h𝔪, LinearMap.mem_ker, map_sub, AdicCompletion.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, eval_of, Submodule.mkQ_apply, hb, sub_self]
  have hmono : ∀ {m m' : ℕ}, m ≤ m' →
      (𝔪 ^ m' • ⊤ : Submodule B (AdicCompletion 𝔪 B)) ≤ 𝔪 ^ m • ⊤ := fun h =>
    Submodule.smul_mono_left (Ideal.pow_le_pow_right h)
  have e : χ₁ x - χ₂ x = χ₁ (x - algebraMap B _ b) - χ₂ (x - algebraMap B _ b) := by
    have hab : χ₁ (algebraMap B _ b) = χ₂ (algebraMap B _ b) := by
      rw [← RingHom.comp_apply, hagree, RingHom.comp_apply]
    rw [map_sub, map_sub, hab]; ring
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, e]
  exact sub_mem (hn₁ _ (hmono (le_max_left _ _) hker)) (hn₂ _ (hmono (le_max_right _ _) hker))

theorem forall_mem_smul_top_imp {B : Type*} [CommRing B] (𝔪 : Ideal B) {S : Type*} [CommRing S] (J : Ideal S)
    (χ : AdicCompletion 𝔪 B →+* S) (n k : ℕ) (h : 𝔪 ^ n ≤ (J ^ k).comap (χ.comp (algebraMap B _))) :
    ∀ x ∈ (𝔪 ^ n • ⊤ : Submodule B (AdicCompletion 𝔪 B)), χ x ∈ J ^ k := by
  intro x hx
  refine Submodule.smul_induction_on (p := fun x => χ x ∈ J ^ k) hx ?_ ?_
  · intro r hr y _
    change χ (r • y) ∈ J ^ k
    rw [Algebra.smul_def, map_mul]
    exact Ideal.mul_mem_right _ _ (h hr)
  · intro x y hx hy
    change χ (x + y) ∈ J ^ k
    rw [map_add]; exact add_mem hx hy

end AdicCompletion.ValuedLift

namespace DVRValued

variable {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
variable {C : Type*} [Field C] [Algebra W C] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation C Γ₀)

theorem lt_one_iff_and_eq_zero_imp {π : W} (hπ : Irreducible π) (hint : ∀ a : W, v (algebraMap W C a) ≤ 1)
    (hπ1 : v (algebraMap W C π) < 1) (hπ0 : v (algebraMap W C π) ≠ 0) :
    (∀ a : W, v (algebraMap W C a) < 1 ↔ a ∈ IsLocalRing.maximalIdeal W) ∧
      (∀ a : W, v (algebraMap W C a) = 0 → a = 0) := by
  have hunit : ∀ a : W, IsUnit a → v (algebraMap W C a) = 1 := by
    intro a ha
    obtain ⟨u, rfl⟩ := ha
    have hprod : v (algebraMap W C u) * v (algebraMap W C ↑u⁻¹) = 1 := by
      rw [← Valuation.map_mul, ← map_mul, Units.mul_inv, map_one, Valuation.map_one]
    refine le_antisymm (hint u) ?_
    by_contra hlt
    push Not at hlt
    have : v (algebraMap W C u) * v (algebraMap W C ↑u⁻¹) < 1 := by
      calc v (algebraMap W C u) * v (algebraMap W C ↑u⁻¹) ≤ v (algebraMap W C u) * 1 :=
            mul_le_mul_right (hint _) _
        _ = v (algebraMap W C u) := mul_one _
        _ < 1 := hlt
    rw [hprod] at this
    exact (lt_irrefl _) this
  have hmax : IsLocalRing.maximalIdeal W = Ideal.span {π} := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  refine ⟨fun a => ⟨fun h => ?_, fun h => ?_⟩, fun a h => ?_⟩
  · by_contra hn
    have hu : IsUnit a := by
      by_contra hu; exact hn ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hu))
    rw [hunit a hu] at h
    exact (lt_irrefl _) h
  · rw [hmax, Ideal.mem_span_singleton] at h
    obtain ⟨b, rfl⟩ := h
    rw [map_mul, Valuation.map_mul]
    calc v (algebraMap W C π) * v (algebraMap W C b) ≤ v (algebraMap W C π) * 1 := mul_le_mul_right (hint b) _
      _ < 1 := by rw [mul_one]; exact hπ1
  · by_contra ha
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
    rw [map_mul, map_pow, Valuation.map_mul, Valuation.map_pow, hunit _ u.isUnit, one_mul] at h
    exact pow_ne_zero n hπ0 h

end DVRValued

end Generic

section Dedekind

namespace Algebra p2m_export "Algebra" "commutes mk algebraMap algebraMap_self smul_def commutes'" end Algebra
p2m_open_scoped "Algebra" in

theorem Algebra.card_algHom_le_finrank_of_free {Ô : Type*} [CommRing Ô] [Nontrivial Ô] {C : Type*} [Field C] [Algebra Ô C]
    (T : Type*) [CommRing T] [Algebra Ô T] [Module.Free Ô T] [Module.Finite Ô T]
    (Φ : Finset (T →ₐ[Ô] C)) : Φ.card ≤ Module.finrank Ô T := by
  classical
  letI := Module.Free.ChooseBasisIndex.fintype Ô T
  let b := Module.Free.chooseBasis Ô T

  have hli : LinearIndependent C (fun φ : Φ => fun i => (φ : T →ₐ[Ô] C) (b i)) := by
    have h0 : LinearIndependent C (fun φ : Φ => ((φ : T →ₐ[Ô] C) : T → C)) := by
      have h := (linearIndependent_monoidHom T C).comp (fun φ : Φ => (φ : T →ₐ[Ô] C).toMonoidHom) (by
        intro φ ψ h
        apply Subtype.ext
        apply AlgHom.ext
        intro t
        exact DFunLike.congr_fun h t)
      exact h
    rw [linearIndependent_iff'] at h0 ⊢
    intro s g hg φ hφ
    apply h0 s g _ φ hφ
    ext t
    have hgi : ∀ i, ∑ ψ ∈ s, g ψ * (ψ : T →ₐ[Ô] C) (b i) = 0 := fun i => by
      have := congr_fun hg i
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using this
    have ht : ∀ ψ : T →ₐ[Ô] C, ψ t = ∑ i, algebraMap Ô C (b.repr t i) * ψ (b i) := by
      intro ψ
      conv_lhs => rw [← b.sum_repr t]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, Algebra.smul_def]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    simp_rw [ht, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    have : ∑ ψ ∈ s, g ψ * (algebraMap Ô C (b.repr t i) * (ψ : T →ₐ[Ô] C) (b i))
        = algebraMap Ô C (b.repr t i) * ∑ ψ ∈ s, g ψ * (ψ : T →ₐ[Ô] C) (b i) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun ψ _ => ?_; ring
    rw [this, hgi i, mul_zero]
  have hcard := hli.fintype_card_le_finrank
  rw [Fintype.card_coe, Module.finrank_fintype_fun_eq_card] at hcard
  rw [Module.finrank_eq_card_chooseBasisIndex]
  exact hcard

namespace Module p2m_export "Module" "Injective Free.chooseBasis Free.ChooseBasisIndex isTorsionFree_iff_algebraMap_injective equiv finrank Free mk IsTorsionFree free_of_finite_type_torsion_free' Finite.of_surjective finrank_fintype_fun_eq_card finrank_eq_card_chooseBasisIndex Free.ChooseBasisIndex.fintype" namespace Finite p2m_export "Module.Finite" "equiv trans map of_surjective quotient" end Module.Finite
p2m_open_scoped "Module Module.Finite" in

theorem Module.Finite.quotient_of_le {W : Type*} [CommRing W] {R : Type*} [CommRing R] [Algebra W R]
    {J Q : Ideal R} (h : J ≤ Q) [Module.Finite W (R ⧸ J)] : Module.Finite W (R ⧸ Q) := by
  refine Module.Finite.of_surjective (Ideal.Quotient.factorₐ W h).toLinearMap ?_
  intro x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk J z, rfl⟩

namespace AlgHom p2m_export "AlgHom" "codRestrict ext commutes toLinearMap id_apply comp Finite.of_surjective mk toRingHom card Finite commutes' comp_apply" end AlgHom
p2m_open_scoped "AlgHom" in

theorem AlgHom.exists_quotient_lift_injective {W : Type*} [CommRing W] {R : Type*} [CommRing R] [Algebra W R]
    {C : Type*} [CommRing C] [Algebra W C] (Q : Ideal R) (χ : R →ₐ[W] C) (hQ : ∀ z, z ∈ Q ↔ χ z = 0) :
    ∃ φ : (R ⧸ Q) →ₐ[W] C, Function.Injective φ ∧ ∀ z, φ (Ideal.Quotient.mk Q z) = χ z := by
  refine ⟨Ideal.Quotient.liftₐ Q χ (fun z hz => (hQ z).mp hz), ?_, fun z => rfl⟩
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hQ z).mpr hz)

end Dedekind

namespace ModularCurve p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar ModularPolynomialData modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence ssPlaces NodeLocalized.coeffSubring UVCrossingModel PlaceSpecialization.ProlongationTuple.valuation_coe_lt_one_of_maximalIdeal_eq_span" namespace PlaceSpecialization p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple reduceFst mk ProlongationTuple.valuation_coe_lt_one_of_maximalIdeal_eq_span" namespace ProlongationTuple p2m_export "ModularCurve.PlaceSpecialization.ProlongationTuple" "ValueIntegralityLaw nodeIntegersOver nodeConst NodeCoordinates mk ι valuation_coe_lt_one_of_maximalIdeal_eq_span" end ModularCurve.PlaceSpecialization.ProlongationTuple
namespace ModularCurve.PlaceSpecialization.ProlongationTuple
p2m_open_scoped "ModularCurve ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple" in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in
open Valued ModularCurve.UVCrossingModel _root_.ModularCurve.PlaceSpecialization.ProlongationTuple AdicCompletion.ValuedLift in

private theorem _root_.ModularCurve.PlaceSpecialization.ProlongationTuple.exists_algHom_of_completedEvaluation
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [PerfectField k]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    [IsLocalRing ↥(R.nodeIntegersOver K w)]
    {W : Type u} [CommRing W]
    (π : W) (E : ℕ)
    (ι : AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)
          ≃+* UVCrossingModel W (π ^ E))
    (αU : UVCrossingModel W (π ^ E)) (hιx : ι (algebraMap _ _ c.x) = U (π ^ E) * αU)
    [IsLocalRing ↥(NodeLocalized.coeffSubring A K)]
    (hϖgen : IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K) = Ideal.span {ϖ})
    (τ : AdicCompletion (IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K))
        ↥(NodeLocalized.coeffSubring A K) ≃+* W)
    (hτo : ∀ o : ↥(NodeLocalized.coeffSubring A K),
        ι (algebraMap _ _ (R.nodeConst K w o)) = const (π ^ E) (τ (algebraMap _ _ o)))
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (ψ : AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w) →+* 𝒪[(A.valuation).Completion])

    (ιC : AlgebraicClosure ℚ →+* (A.valuation).Completion)
    (hψ' : ∀ g : ↥(R.nodeIntegersOver K w),
      ((ψ (algebraMap _ _ g) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) = ιC (V.evalAt ((g : ↥(modularFunctionFieldBar (N * q))))))
    (ϖC : 𝒪[(A.valuation).Completion])
    (hϖC : (ϖC : (A.valuation).Completion) = ιC ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ))
    [IsAdicComplete (Ideal.span {ϖC}) 𝒪[(A.valuation).Completion]]
    (ιOC : AdicCompletion (IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K)) ↥(NodeLocalized.coeffSubring A K)
        →+* 𝒪[(A.valuation).Completion])
    (hιOC : ∀ o : ↥(NodeLocalized.coeffSubring A K),
        ((ιOC (algebraMap _ _ o) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) =
          ιC ((o : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ))
    [Algebra W (A.valuation).Completion]
    (halg : ∀ a : W, algebraMap W (A.valuation).Completion a =
        ((ιOC (τ.symm a) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion)) :
    ∃ φ : UVCrossingModel W (π ^ E) →ₐ[W] (A.valuation).Completion,
      (∀ z, φ z = ((ψ (ι.symm z) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion)) ∧
      (∀ g : ↥(R.nodeIntegersOver K w),
        φ (ι (algebraMap _ _ g)) = ιC (V.evalAt ((g : ↥(modularFunctionFieldBar (N * q)))))) ∧
      φ (U (π ^ E) * αU) = ιC (V.evalAt ((c.x : ↥(modularFunctionFieldBar (N * q))))) := by
  classical

  let χ : UVCrossingModel W (π ^ E) →+* (A.valuation).Completion :=
    ((𝒪[(A.valuation).Completion]).subtype.comp ψ).comp ι.symm.toRingHom
  have hχι : ∀ y, χ (ι y) = ((ψ y : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) := fun y => by
    show ((ψ (ι.symm (ι y)) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) = _
    rw [RingEquiv.symm_apply_apply]

  let χ₁ : AdicCompletion (IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K)) ↥(NodeLocalized.coeffSubring A K)
      →+* 𝒪[(A.valuation).Completion] :=
    ψ.comp (ι.symm.toRingHom.comp ((algebraMap W (UVCrossingModel W (π ^ E))).comp τ.toRingHom))
  have hconst : ∀ a : W, algebraMap W (UVCrossingModel W (π ^ E)) a = const (π ^ E) a := fun a => rfl
  have hχ₁o : ∀ o : ↥(NodeLocalized.coeffSubring A K),
      χ₁ (algebraMap _ _ o) = ψ (algebraMap _ _ (R.nodeConst K w o)) := by
    intro o
    show ψ (ι.symm (algebraMap W _ (τ (algebraMap _ _ o)))) = _
    rw [hconst, ← hτo, RingEquiv.symm_apply_apply]
  have hevconst : ∀ o : ↥(NodeLocalized.coeffSubring A K),
      V.evalAt ((R.nodeConst K w o : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) =
        ((o : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) := fun o =>
    V.evalAt_algebraMap _
  have hagree : χ₁.comp (algebraMap _ _) = ιOC.comp (algebraMap ↥(NodeLocalized.coeffSubring A K) _) := by
    apply RingHom.ext
    intro o
    show χ₁ (algebraMap _ _ o) = ιOC (algebraMap _ _ o)
    apply Subtype.ext
    rw [hχ₁o, hψ', hevconst, hιOC]
  have hϖ₁ : χ₁ (algebraMap _ _ ϖ) = ϖC := Subtype.ext (by rw [hχ₁o, hψ', hevconst, hϖC])
  have hϖ₂ : ιOC (algebraMap _ _ ϖ) = ϖC := Subtype.ext (by rw [hιOC, hϖC])
  have hcontχ : ∀ χ' : AdicCompletion (IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K))
      ↥(NodeLocalized.coeffSubring A K) →+* 𝒪[(A.valuation).Completion], χ' (algebraMap _ _ ϖ) = ϖC →
      ∀ k' : ℕ, ∃ n : ℕ, ∀ x ∈ (IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K) ^ n • ⊤ :
        Submodule ↥(NodeLocalized.coeffSubring A K) (AdicCompletion (IsLocalRing.maximalIdeal
          ↥(NodeLocalized.coeffSubring A K)) ↥(NodeLocalized.coeffSubring A K))), χ' x ∈ Ideal.span {ϖC} ^ k' := by
    intro χ' hχ' k'
    refine ⟨k', forall_mem_smul_top_imp _ _ χ' k' k' ?_⟩
    intro a ha
    rw [hϖgen, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [Ideal.mem_comap, RingHom.comp_apply, map_mul, map_pow, map_mul, map_pow, hχ', Ideal.span_singleton_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton.mpr (dvd_refl _))
  haveI : IsHausdorff (Ideal.span {ϖC}) 𝒪[(A.valuation).Completion] := IsAdicComplete.toIsHausdorff
  have hFG : (IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K)).FG :=
    ⟨{ϖ}, by rw [hϖgen, Finset.coe_singleton]⟩
  have hχeq : χ₁ = ιOC :=
    ringHom_ext_of_comp_algebraMap_eq _ hFG _ χ₁ ιOC hagree (hcontχ χ₁ hϖ₁) (hcontχ ιOC hϖ₂)

  have hcommR : ∀ a : W, χ (algebraMap W (UVCrossingModel W (π ^ E)) a) = algebraMap W (A.valuation).Completion a := by
    intro a
    rw [halg, ← hχeq]
    show ((ψ (ι.symm (algebraMap W _ a)) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) =
      ((ψ (ι.symm (algebraMap W _ (τ (τ.symm a)))) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion)
    rw [RingEquiv.apply_symm_apply]
  let χₐ : UVCrossingModel W (π ^ E) →ₐ[W] (A.valuation).Completion := { toRingHom := χ, commutes' := hcommR }
  refine ⟨χₐ, fun z => rfl, fun g => ?_, ?_⟩
  · show χ (ι (algebraMap _ _ g)) = _
    rw [hχι, hψ']
  · show χ (U (π ^ E) * αU) = _
    rw [← hιx, hχι, hψ']

end ModularCurve.PlaceSpecialization.ProlongationTuple
p2m_export "" "ModularCurve.PlaceSpecialization.ProlongationTuple.exists_algHom_of_completedEvaluation"
set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 800000 in
open ModularCurve.UVCrossingModel Valued in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [PerfectField k]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K)) (hϖ0 : ϖ ≠ 0)
    [IsLocalRing ↥(R.nodeIntegersOver K w)] [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (hmax : IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hres : ∀ g : ↥(R.nodeIntegersOver K w), ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o))
    (hVI : R.ValueIntegralityLaw w) [DecidableEq k] (hwss : w ∈ ssPlaces q N k)
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)
          ≃+* UVCrossingModel W (π ^ E))
    (hιϖ : ι (algebraMap _ _ (R.nodeConst K w ϖ)) = const (π ^ E) π)
    (αU : UVCrossingModel W (π ^ E)) (hαU : IsUnit αU) (hιx : ι (algebraMap _ _ c.x) = U (π ^ E) * αU)
    [IsDiscreteValuationRing ↥(NodeLocalized.coeffSubring A K)]
    (hϖgen : IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K) = Ideal.span {ϖ})
    (hτ : ∃ τ : AdicCompletion (IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K))
        ↥(NodeLocalized.coeffSubring A K) ≃+* W,
      (∀ o : ↥(NodeLocalized.coeffSubring A K),
        ι (algebraMap _ _ (R.nodeConst K w o)) = const (π ^ E) (τ (algebraMap _ _ o))) ∧
      τ (algebraMap _ _ ϖ) = π)
    (𝔮 : Ideal ↥(R.nodeIntegersOver K w))
    (hJfin : Module.Finite W (UVCrossingModel W (π ^ E) ⧸ Ideal.map (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w) (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)))) 𝔮))
    (Q : PrimeSpectrum (UVCrossingModel W (π ^ E)))
    (S : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))))
    (hS : ∀ V ∈ S, P.reduceFst V = w ∧
      (∀ g : ↥(R.nodeIntegersOver K w), g ∈ 𝔮 ↔ V.evalAt ((g : ↥(modularFunctionFieldBar (N * q)))) = 0) ∧
      ∃ ψ : AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w) →+*
          𝒪[(A.valuation).Completion],
        (∀ g : ↥(R.nodeIntegersOver K w),
          ((ψ (algebraMap ↥(R.nodeIntegersOver K w) _ g) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) =
            ((V.evalAt (g : ↥(modularFunctionFieldBar (N * q))) : AlgebraicClosure ℚ) : (A.valuation).Completion)) ∧
        Q.asIdeal = RingHom.ker (ψ.comp ι.symm.toRingHom))
    (hsep : ∀ V ∈ S, ∀ V' ∈ S,
      (∀ g : ↥(R.nodeIntegersOver K w), V.evalAt ((g : ↥(modularFunctionFieldBar (N * q))))
        = V'.evalAt ((g : ↥(modularFunctionFieldBar (N * q))))) → V = V') :
    (S.card : ℕ∞) ≤ (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞) := by
  classical
  obtain ⟨τ, hτo, hτϖ⟩ := hτ

  obtain ⟨ιC, hιC, hvC⟩ : ∃ ιC : AlgebraicClosure ℚ →+* (A.valuation).Completion,
      (∀ x, ιC x = (x : (A.valuation).Completion)) ∧ ∀ x, Valued.v (ιC x) = A.valuation x := by
    refine ⟨(UniformSpace.Completion.coeRingHom : WithVal A.valuation →+* (A.valuation).Completion).comp
      (WithVal.equiv A.valuation).symm.toRingHom, fun x => rfl, fun x => ?_⟩
    show Valued.v (((WithVal.equiv A.valuation).symm x : WithVal A.valuation) : (A.valuation).Completion) = A.valuation x
    rw [Valued.valuedCompletion_apply]
    rfl

  have hvϖ1 : A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) < 1 :=
    ModularCurve.PlaceSpecialization.ProlongationTuple.valuation_coe_lt_one_of_maximalIdeal_eq_span R K w c ϖ hmax
  have hϖ0' : ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ≠ 0 := fun h => hϖ0 (Subtype.ext h)
  have hvϖ0 : A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ≠ 0 := by
    rwa [Valuation.ne_zero_iff]
  have hOmem : ∀ x : AlgebraicClosure ℚ, A.valuation x ≤ 1 → ιC x ∈ 𝒪[(A.valuation).Completion] := fun x hx => by
    change Valued.v (ιC x) ≤ 1; rw [hvC]; exact hx
  obtain ⟨ϖC, hϖC⟩ : ∃ ϖC : 𝒪[(A.valuation).Completion],
      (ϖC : (A.valuation).Completion) = ιC ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) :=
    ⟨⟨ιC _, hOmem _ hvϖ1.le⟩, rfl⟩
  have hvϖC : Valued.v (ϖC : (A.valuation).Completion) =
      A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) := by rw [hϖC, hvC]
  have hϖC0 : (ϖC : (A.valuation).Completion) ≠ 0 := by
    rw [hϖC]; exact (map_ne_zero ιC).mpr hϖ0'
  haveI hAC : IsAdicComplete (Ideal.span {ϖC}) 𝒪[(A.valuation).Completion] := by
    apply Valued.isAdicComplete_integer_span_singleton_of_forall_exists_pow_lt ϖC hϖC0
    intro γ hγ
    rw [hvϖC]
    exact A.exists_valuation_pow_lt_of_isAlgebraic hvϖ0 hvϖ1 γ hγ

  obtain ⟨ιOC, hιOC⟩ : ∃ ιOC : AdicCompletion (IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K))
      ↥(NodeLocalized.coeffSubring A K) →+* 𝒪[(A.valuation).Completion],
      ∀ o : ↥(NodeLocalized.coeffSubring A K),
        ((ιOC (algebraMap _ _ o) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) =
          ιC ((o : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) := by
    have hmemO : ∀ o : ↥(NodeLocalized.coeffSubring A K),
        (ιC.comp (NodeLocalized.coeffSubring A K).subtype) o ∈ 𝒪[(A.valuation).Completion] := fun o =>
      hOmem _ (A.valuation_le_one ⟨_, o.2.1⟩)
    let evO' : ↥(NodeLocalized.coeffSubring A K) →+* 𝒪[(A.valuation).Completion] :=
      (ιC.comp (NodeLocalized.coeffSubring A K).subtype).codRestrict _ hmemO
    have hevO'ϖ : evO' ϖ = ϖC := Subtype.ext (by rw [hϖC]; rfl)
    have hcontO : ∀ k' : ℕ, ∃ n : ℕ, IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K) ^ n ≤
        (Ideal.span {ϖC} ^ k').comap evO' := by
      intro k'
      refine ⟨k', fun a ha => ?_⟩
      rw [hϖgen, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha
      obtain ⟨b, rfl⟩ := ha
      rw [Ideal.mem_comap, map_mul, map_pow, hevO'ϖ, Ideal.span_singleton_pow]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton.mpr (dvd_refl _))
    obtain ⟨ιOC, hιOCcomp⟩ := AdicCompletion.exists_ringHom_comp_algebraMap_eq_of_forall_exists_pow_le_comap
      (IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K)) (Ideal.span {ϖC}) evO' hcontO
    refine ⟨ιOC, fun o => ?_⟩
    have : ιOC (algebraMap _ _ o) = evO' o := by rw [← RingHom.comp_apply, hιOCcomp]
    rw [this]
    rfl

  letI algWC : Algebra W (A.valuation).Completion :=
    ((𝒪[(A.valuation).Completion]).subtype.comp (ιOC.comp τ.symm.toRingHom)).toAlgebra
  have halg : ∀ a : W, algebraMap W (A.valuation).Completion a =
      ((ιOC (τ.symm a) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) := fun a => rfl
  have hτsymm : τ.symm π = algebraMap _ _ ϖ := by rw [RingEquiv.symm_apply_eq, hτϖ]
  have hπC : algebraMap W (A.valuation).Completion π =
      ιC ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) := by rw [halg, hτsymm, hιOC]
  have hvπ : Valued.v (algebraMap W (A.valuation).Completion π) =
      A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) := by rw [hπC, hvC]
  obtain ⟨hv, hv0⟩ := DVRValued.lt_one_iff_and_eq_zero_imp (Valued.v : Valuation (A.valuation).Completion _) hπ
    (fun a => by rw [halg]; exact (ιOC (τ.symm a)).2) (by rw [hvπ]; exact hvϖ1) (by rw [hvπ]; exact hvϖ0)
  have hinjW : Function.Injective (algebraMap W (A.valuation).Completion) := by
    intro a b h
    rw [← sub_eq_zero] at h ⊢
    rw [← map_sub] at h
    exact hv0 _ (by rw [h, Valuation.map_zero])

  have key : ∀ V ∈ S, ∃ φ : (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) →ₐ[W] (A.valuation).Completion,
      Function.Injective φ ∧
      (∀ g : ↥(R.nodeIntegersOver K w),
        φ (Ideal.Quotient.mk Q.asIdeal (ι (algebraMap _ _ g))) = ιC (V.evalAt ((g : ↥(modularFunctionFieldBar (N * q)))))) ∧
      Ideal.map (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
        (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)))) 𝔮 ≤ Q.asIdeal := by
    intro V hVS
    obtain ⟨hVw, h𝔮V, ψ, hψ, hQ⟩ := hS V hVS
    have hψ' : ∀ g : ↥(R.nodeIntegersOver K w),
        ((ψ (algebraMap _ _ g) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) =
          ιC (V.evalAt ((g : ↥(modularFunctionFieldBar (N * q))))) := fun g => by rw [hψ, hιC]
    obtain ⟨χ, hχψ, hχg, -⟩ := R.exists_algHom_of_completedEvaluation K w c ϖ π E ι αU hιx hϖgen τ hτo V ψ ιC hψ'
      ϖC hϖC ιOC hιOC halg
    have hmemQ : ∀ z : UVCrossingModel W (π ^ E), z ∈ Q.asIdeal ↔ χ z = 0 := by
      intro z
      rw [hQ, RingHom.mem_ker, hχψ]
      show ψ (ι.symm z) = 0 ↔ ((ψ (ι.symm z) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) = 0
      exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩
    obtain ⟨φ, hφinj, hφmk⟩ := AlgHom.exists_quotient_lift_injective Q.asIdeal χ hmemQ
    refine ⟨φ, hφinj, fun g => by rw [hφmk, hχg], ?_⟩
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, hmemQ]
    show χ (ι (algebraMap _ _ g)) = 0
    rw [hχg, (h𝔮V g).mp hg, map_zero]

  rcases S.eq_empty_or_nonempty with hS0 | ⟨V₀, hV₀⟩
  · rw [hS0, Finset.card_empty, Nat.cast_zero]
    exact zero_le
  choose Φf hΦf using key

  have hinj : Function.Injective (fun V : {V // V ∈ S} => Φf V.1 V.2) := by
    intro V V' hEq
    apply Subtype.ext
    apply hsep V.1 V.2 V'.1 V'.2
    intro g
    have h1 := (hΦf V.1 V.2).2.1 g
    have h2 := (hΦf V'.1 V'.2).2.1 g
    have hEq' : Φf V.1 V.2 = Φf V'.1 V'.2 := hEq
    rw [hEq'] at h1
    exact ιC.injective (h1.symm.trans h2)
  have hcard : (S.attach.image (fun V : {V // V ∈ S} => Φf V.1 V.2)).card = S.card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_attach]

  obtain ⟨hφ₀inj, -, hJQ⟩ := hΦf V₀ hV₀
  haveI : Module.Finite W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) := Module.Finite.quotient_of_le hJQ
  have hinjT : Function.Injective (algebraMap W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal)) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    apply hinjW
    rw [map_zero, ← (Φf V₀ hV₀).commutes, ha, map_zero]
  haveI : Module.IsTorsionFree W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr hinjT
  haveI : Module.Free W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) := Module.free_of_finite_type_torsion_free'

  have hcount := Algebra.card_algHom_le_finrank_of_free (Ô := W) (C := (A.valuation).Completion)
    (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) (S.attach.image (fun V : {V // V ∈ S} => Φf V.1 V.2))
  rw [hcard] at hcount
  exact_mod_cast hcount

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_card_le_finrank_quotient_of_forall_ker_eq
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_card_le_finrank_quotient_of_forall_ker_eq (solution)
