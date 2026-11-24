-- Prove2me | solution 1 for GlobalTheory.unramExt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:41:22.877791+00:00
-- url     : https://prove2.me/submissions/24ad2f40-4b3d-4d94-b896-f68555a3d728

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFiniteEtaleLocalSurjectiveOfIsSeparable
import Theorems.Thm_GlobalTheory_exists_isDiscreteValuationRing_of_flat
import Theorems.Thm_GlobalTheory_isUnit_adjoinRoot_mk_of_aeval_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GlobalTheory
open Polynomial IsLocalRing
open Polynomial IsLocalRing in
private lemma mem_smul_top_iff_of_linearEquiv_pi {V M ι : Type*} [CommRing V] [AddCommGroup M]
    [Module V M] [Fintype ι] [DecidableEq ι] (e : M ≃ₗ[V] (ι → V)) (J : Ideal V) (x : M) :
    x ∈ J • (⊤ : Submodule V M) ↔ ∀ i, e x i ∈ J := by
  constructor
  · intro hx
    have hle : J • (⊤ : Submodule V M) ≤
        (Submodule.pi Set.univ (fun _ : ι => J)).comap e.toLinearMap := by
      refine Submodule.smul_le.mpr fun r hr m _ => ?_
      simp only [Submodule.mem_comap, Submodule.mem_pi, Set.mem_univ, true_implies,
        LinearEquiv.coe_coe, map_smul, Pi.smul_apply, smul_eq_mul]
      exact fun i => J.mul_mem_right _ hr
    intro i
    have := hle hx
    simp only [Submodule.mem_comap, Submodule.mem_pi, Set.mem_univ, true_implies,
      LinearEquiv.coe_coe] at this
    exact this i
  · intro hx
    have hsum : x = ∑ i, e x i • e.symm (fun j => if i = j then 1 else 0) := by
      apply e.injective
      simp only [map_sum, map_smul, LinearEquiv.apply_symm_apply]
      exact pi_eq_sum_univ (e x)
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top
open Polynomial IsLocalRing in
private lemma ideal_smul_top_eq_self {V : Type*} [CommRing V] (J : Ideal V) :
    J • (⊤ : Submodule V V) = J := by
  rw [smul_eq_mul, Ideal.mul_top]
open Polynomial IsLocalRing in
private lemma isAdicComplete_of_linearEquiv_pi {V M ι : Type*} [CommRing V] [AddCommGroup M]
    [Module V M] [Fintype ι] (e : M ≃ₗ[V] (ι → V)) (J : Ideal V) [IsAdicComplete J V] :
    IsAdicComplete J M := by
  classical
  have key : ∀ (n : ℕ) (x y : M), x ≡ y [SMOD J ^ n • (⊤ : Submodule V M)] ↔
      ∀ i, e x i ≡ e y i [SMOD J ^ n • (⊤ : Submodule V V)] := by
    intro n x y
    simp only [SModEq.sub_mem, mem_smul_top_iff_of_linearEquiv_pi e, map_sub, Pi.sub_apply,
      ideal_smul_top_eq_self]
  refine { haus' := fun x hx => ?_, prec' := fun f hf => ?_ }
  · apply e.injective
    funext i
    rw [map_zero]
    exact IsHausdorff.haus' (I := J) (e x i) fun n => by
      simpa using (key n x 0).1 (hx n) i
  · choose L hL using fun i => IsPrecomplete.prec' (I := J) (fun n => e (f n) i)
      (fun {m n} hmn => (key m _ _).1 (hf hmn) i)
    refine ⟨e.symm L, fun n => (key n _ _).2 fun i => ?_⟩
    simpa using hL i n
end GlobalTheory
end

set_option autoImplicit false
open GlobalTheory
open Polynomial IsLocalRing
open Polynomial IsLocalRing
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : _root_.ReciprocityTheory.ChartRestriction.G.Out.UnramExtSt := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Out.UnramExtSt
  intro V _ _ _ _ k' _ _ _ _
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element (ResidueField V) k'
  have hint : IsIntegral (ResidueField V) θ := .of_finite _ _
  obtain ⟨μ, hμmap, hμdeg, hμ⟩ := lifts_and_degree_eq_and_monic
    (map_surjective _ (residue_surjective (R := V)) (minpoly (ResidueField V) θ))
    (minpoly.monic hint)
  letI : Algebra V k' := ((algebraMap (ResidueField V) k').comp (residue V)).toAlgebra
  haveI : IsScalarTower V (ResidueField V) k' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hroot : eval₂ (algebraMap V k') θ μ = 0 := by
    rw [show algebraMap V k' = (algebraMap (ResidueField V) k').comp (residue V) from rfl,
      ← eval₂_map, hμmap]
    exact minpoly.aeval _ _
  let φ : AdjoinRoot μ →+* k' := AdjoinRoot.lift (algebraMap V k') θ hroot
  have hφ : ∀ g : V[X], φ (AdjoinRoot.mk μ g) = aeval θ g := fun g => by
    simp [φ, AdjoinRoot.lift_mk, aeval_def]
  have hadj : Algebra.adjoin (ResidueField V) {θ} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hθ]; rfl
  have hsurj : Function.Surjective φ := by
    intro y
    have hy : y ∈ Algebra.adjoin (ResidueField V) {θ} := hadj ▸ Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨p, rfl⟩ := hy
    obtain ⟨q, rfl⟩ := map_surjective _ (residue_surjective (R := V)) p
    refine ⟨AdjoinRoot.mk μ q, ?_⟩
    rw [hφ]
    simp [aeval_def, eval₂_map, IsScalarTower.algebraMap_eq V (ResidueField V) k']
  haveI : Nontrivial (AdjoinRoot μ) := φ.domain_nontrivial
  have hnon : ∀ w : AdjoinRoot μ, w ∈ nonunits (AdjoinRoot μ) ↔ φ w = 0 := by
    intro w
    refine ⟨fun hw => ?_, fun hw hu => (hu.map φ).ne_zero hw⟩
    by_contra hne
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective w
    rw [hφ] at hne
    exact hw (_root_.GlobalTheory.isUnit_adjoinRoot_mk_of_aeval_ne_zero hint hμ hμmap hne)
  haveI : IsLocalRing (AdjoinRoot μ) := IsLocalRing.of_nonunits_add fun a b ha hb => by
    rw [hnon] at ha hb ⊢
    rw [map_add, ha, hb, add_zero]
  have hmax : maximalIdeal (AdjoinRoot μ) = RingHom.ker φ := by
    ext w
    rw [mem_maximalIdeal, hnon, RingHom.mem_ker]
  have hCm : (AdjoinRoot.mk μ).comp C = algebraMap V (AdjoinRoot μ) := rfl
  have hker : RingHom.ker φ = (maximalIdeal V).map (algebraMap V (AdjoinRoot μ)) := by
    apply le_antisymm
    · intro w hw
      obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective w
      rw [RingHom.mem_ker, hφ] at hw
      have hdvd : minpoly (ResidueField V) θ ∣ g.map (residue V) := by
        apply minpoly.dvd
        rw [← IsLocalRing.ResidueField.algebraMap_eq, aeval_map_algebraMap]
        exact hw
      obtain ⟨h', hh'⟩ := hdvd
      obtain ⟨h, rfl⟩ := map_surjective _ (residue_surjective (R := V)) h'
      have hcoeff : ∀ n, (g - μ * h).coeff n ∈ maximalIdeal V := by
        intro n
        rw [← residue_eq_zero_iff, ← coeff_map, Polynomial.map_sub, Polynomial.map_mul, hμmap,
          hh', sub_self, coeff_zero]
      have hmk : AdjoinRoot.mk μ g = AdjoinRoot.mk μ (g - μ * h) := by
        simp [AdjoinRoot.mk_self]
      rw [hmk, ← hCm, ← Ideal.map_map]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_C_iff.2 hcoeff)
    · rw [Ideal.map_le_iff_le_comap]
      intro v hv
      rw [Ideal.mem_comap, RingHom.mem_ker, ← hCm, RingHom.comp_apply, hφ, aeval_C,
        IsScalarTower.algebraMap_apply V (ResidueField V) k',
        IsLocalRing.ResidueField.algebraMap_eq, (residue_eq_zero_iff v).2 hv, map_zero]
  have hmW : maximalIdeal (AdjoinRoot μ) = (maximalIdeal V).map (algebraMap V (AdjoinRoot μ)) :=
    hmax.trans hker
  let pb := AdjoinRoot.powerBasis' hμ
  haveI : Module.Finite V (AdjoinRoot μ) := pb.finite
  haveI : Module.Free V (AdjoinRoot μ) := Module.Free.of_basis pb.basis
  haveI : IsNoetherianRing (AdjoinRoot μ) := inferInstance
  have hinj : Function.Injective (algebraMap V (AdjoinRoot μ)) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    rw [← hCm, RingHom.comp_apply, AdjoinRoot.mk_eq_zero] at hv
    by_contra hne
    have hle := degree_le_of_dvd hv (C_ne_zero.2 hne)
    rw [degree_C hne, hμdeg] at hle
    exact absurd hle (not_le.2 (minpoly.degree_pos hint))
  haveI hlh : IsLocalHom (algebraMap V (AdjoinRoot μ)) := by
    refine ⟨fun v hv => ?_⟩
    by_contra hnu
    have hvm : v ∈ maximalIdeal V := (mem_maximalIdeal v).2 hnu
    have := Ideal.mem_map_of_mem (algebraMap V (AdjoinRoot μ)) hvm
    rw [← hmW] at this
    exact (mem_maximalIdeal _).1 this hv
  let e : ResidueField (AdjoinRoot μ) ≃+* k' :=
    (Ideal.quotEquivOfEq hmax).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  have he : ∀ w, e (residue (AdjoinRoot μ) w) = φ w := fun w => rfl
  have he' : ∀ v : V, e (residue (AdjoinRoot μ) (algebraMap V (AdjoinRoot μ) v)) =
      algebraMap (ResidueField V) k' (residue V v) := by
    intro v
    rw [he, ← hCm, RingHom.comp_apply, hφ, aeval_C]
    rfl
  let eAlg : ResidueField (AdjoinRoot μ) →ₐ[ResidueField V] k' :=
    { e.toRingHom with
      commutes' := fun r => by
        obtain ⟨v, rfl⟩ := residue_surjective r
        simpa using he' v }
  haveI : Algebra.IsSeparable (ResidueField V) (ResidueField (AdjoinRoot μ)) :=
    Algebra.IsSeparable.of_algHom _ _ eAlg
  haveI : Algebra.FormallyUnramified V (AdjoinRoot μ) :=
    Algebra.FormallyUnramified.of_map_maximalIdeal hmW.symm
  obtain ⟨hdom, hdvr⟩ := _root_.GlobalTheory.exists_isDiscreteValuationRing_of_flat V (AdjoinRoot μ) hmW.symm
    (Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal _).ne_top)
  have hcompl : IsAdicComplete (maximalIdeal (AdjoinRoot μ)) (AdjoinRoot μ) := by
    rw [hmW, IsAdicComplete.map_algebraMap_iff]
    exact isAdicComplete_of_linearEquiv_pi pb.basis.equivFun _
  exact ⟨AdjoinRoot μ, inferInstance, hdom, hdvr, hcompl, inferInstance, pb.finite, hinj, hlh,
    inferInstance, e, he'⟩
end _root_.GlobalTheory
end GlobalTheory
