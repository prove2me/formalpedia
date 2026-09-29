-- Prove2me | solution 1 for ModularCurve.FullLevel.Diamond.pernodeConclusion_of_pernodeHyps_of_rigidChart_linkedScalars_of_eq_three_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/d20a06db-f6f4-5ebf-9dfa-7dbd70ceed08

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_AdicCompletionLocalRing
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_AlgebraicCurve_BaseChangeGalois

import Theorems.Thm_IsLocalRing_exists_ringHom_adicCompletion_inf_fixedPoints_range_eq_of_isLocalization
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_algHom_range_eq_fixedPoints_apply_U_apply_V_of_tangent
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_mul_eq_pow_mul_and_maximalIdeal_eq_span_of_ringEquiv_adicCompletion_pow
import Theorems.Thm_ModularCurve_UVCrossingModel_mem_iff_ringEquiv_adicCompletion_mem_span_or_swap_of_ne
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_comap_of_mem_of_not_isUnit
import Theorems.Thm_IsLocalRing_exists_ringHom_ringEquiv_adicCompletion_uvCrossingModel_of_ringEquiv
import Theorems.Thm_IsLocalRing_exists_branchReadings_of_ringEquiv_adicCompletion_uvCrossingModel_pow
import Theorems.Thm_ModularCurve_UVCrossingModel_dvd_and_exists_eq_mul_pow_of_apply_eq_mul_pow_of_range_eq_fixedPoints
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_Diamond_pernodeConclusion_of_pernodeHyps_of_rigidChart_linkedScalars_of_eq_three_of_dvd
p2m_attr_erase "simp" "AdicCompletion.map_smul_of AdicCompletion.algebraMap_of AdicCompletion.stabilizer_smul_of AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 0

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup AlgebraicCurve.TwoChartIntegralModel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open ModularCurve.UVCrossingModel

namespace S3C4Pernode

theorem isUnit_subring_mk_iff {L : Type*} [Field L] (S : Subring L) (x : L) (hx : x ∈ S) :
    IsUnit (⟨x, hx⟩ : ↥S) ↔ x ≠ 0 ∧ x⁻¹ ∈ S := by
  constructor
  · rintro ⟨u, hu⟩
    have e : (((u⁻¹ : (↥S)ˣ) : ↥S) : L) * x = 1 := by
      have := congrArg (fun z : ↥S => (z : L)) u.inv_mul; rw [hu] at this; exact this
    have hx0 : x ≠ 0 := fun h0 => by rw [h0, mul_zero] at e; exact zero_ne_one e
    refine ⟨hx0, ?_⟩
    rw [← eq_inv_of_mul_eq_one_left e]; exact ((u⁻¹ : (↥S)ˣ) : ↥S).2
  · rintro ⟨hx0, hinv⟩
    exact isUnit_iff_exists_inv.mpr ⟨⟨x⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩

noncomputable def subringEquivOfMemIff {F K : Type*} [Field F] [Field K] (ι : F →+* K)
    (V : Subring F) (W : Subring K) (hVW : ∀ f : F, f ∈ V ↔ ι f ∈ W) (hsurj : ∀ g : K, g ∈ W → ∃ f : F, ι f = g) :
    ↥V ≃+* ↥W :=
  RingEquiv.ofBijective
    ({ toFun := fun f => ⟨ι f, (hVW f).mp f.2⟩
       map_one' := Subtype.ext (by change ι 1 = 1; exact map_one ι)
       map_mul' := fun a b => Subtype.ext (by change ι (a * b) = ι a * ι b; exact map_mul ι _ _)
       map_zero' := Subtype.ext (by change ι 0 = 0; exact map_zero ι)
       map_add' := fun a b => Subtype.ext (by change ι (a + b) = ι a + ι b; exact map_add ι _ _) } : ↥V →+* ↥W)
    ⟨fun a b h => Subtype.ext (ι.injective (congrArg Subtype.val h)),
     fun g => by
       obtain ⟨f, hf⟩ := hsurj g g.2
       exact ⟨⟨f, (hVW f).mpr (hf ▸ g.2)⟩, Subtype.ext hf⟩⟩

theorem subringEquivOfMemIff_apply {F K : Type*} [Field F] [Field K] (ι : F →+* K)
    (V : Subring F) (W : Subring K) (hVW : ∀ f : F, f ∈ V ↔ ι f ∈ W) (hsurj : ∀ g : K, g ∈ W → ∃ f : F, ι f = g) (f : ↥V) :
    (subringEquivOfMemIff ι V W hVW hsurj f : K) = ι f := rfl

theorem vs_isUnit_mk_iff {L : Type*} [Field L] (S : ValuationSubring L) (x : L) (hx : x ∈ S) :
    IsUnit (⟨x, hx⟩ : ↥S) ↔ x ≠ 0 ∧ x⁻¹ ∈ S := by
  constructor
  · rintro ⟨u, hu⟩
    have e : (((u⁻¹ : (↥S)ˣ) : ↥S) : L) * x = 1 := by
      have := congrArg (fun z : ↥S => (z : L)) u.inv_mul; rw [hu] at this; exact this
    have hx0 : x ≠ 0 := fun h0 => by rw [h0, mul_zero] at e; exact zero_ne_one e
    refine ⟨hx0, ?_⟩
    rw [← eq_inv_of_mul_eq_one_left e]; exact ((u⁻¹ : (↥S)ˣ) : ↥S).2
  · rintro ⟨hx0, hinv⟩
    exact isUnit_iff_exists_inv.mpr ⟨⟨x⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩

theorem vs_mem_maximalIdeal_iff_of_mem_iff {F K : Type*} [Field F] [Field K] (ι : F →+* K)
    (V : ValuationSubring F) (W : ValuationSubring K) (hVW : ∀ f : F, f ∈ V ↔ ι f ∈ W) (f : F) (hf : f ∈ V) :
    (⟨f, hf⟩ : ↥V) ∈ maximalIdeal ↥V ↔ (⟨ι f, (hVW f).mp hf⟩ : ↥W) ∈ maximalIdeal ↥W := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    vs_isUnit_mk_iff V f hf, vs_isUnit_mk_iff W (ι f) ((hVW f).mp hf), map_ne_zero_iff ι ι.injective, ← map_inv₀, ← hVW]

theorem map_maximalIdeal_eq_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) : (maximalIdeal A).map e.toRingHom = maximalIdeal B := by
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx
    intro hu; apply hx
    have := hu.map e.symm.toRingHom
    simpa using this
  · intro y hy
    have hy' : e.symm y ∈ maximalIdeal A := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
      intro hu; apply hy
      have := hu.map e.toRingHom
      simpa using this
    have := Ideal.mem_map_of_mem e.toRingHom hy'
    simpa using this

theorem evalₐ_ringEquiv_eq_zero {S : Type*} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (e : AdicCompletion (maximalIdeal S) S ≃+* AdicCompletion (maximalIdeal S) S) (n : ℕ)
    (x : AdicCompletion (maximalIdeal S) S) (hx : AdicCompletion.evalₐ (maximalIdeal S) n x = 0) :
    AdicCompletion.evalₐ (maximalIdeal S) n (e x) = 0 := by
  have hker : ∀ y : AdicCompletion (maximalIdeal S) S,
      AdicCompletion.evalₐ (maximalIdeal S) n y = 0 ↔ y ∈ maximalIdeal (AdicCompletion (maximalIdeal S) S) ^ n := by
    intro y
    rw [AdicCompletion.maximalIdeal_pow_eq_ker_evalₐ n, RingHom.mem_ker]
  rw [hker] at hx ⊢
  have h1 : e x ∈ (maximalIdeal (AdicCompletion (maximalIdeal S) S) ^ n).map e.toRingHom :=
    Ideal.mem_map_of_mem e.toRingHom hx
  rwa [Ideal.map_pow, map_maximalIdeal_eq_of_ringEquiv e] at h1

theorem pernode_core
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    (G : Subgroup (K ≃ₐ[k] K)) (hG : Finite ↥G)
    (B : Subring K) (hBG : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ f : K, f ∈ B → σ f ∈ B)
    (BG : Subring K) (hBGdef : ∀ f : K, f ∈ BG ↔ f ∈ B ∧ ∀ σ : K ≃ₐ[k] K, σ ∈ G → σ f = f)
    (hBGnoeth : IsNoetherianRing ↥BG)
    (hfin : ∀ (hle : BG ≤ B), letI := (Subring.inclusion hle).toAlgebra; Module.Finite ↥BG ↥B)
    (Õ : Subring K) [IsLocalRing ↥Õ] (hBÕ : B ≤ Õ)
    (hloc : ∀ f : K, f ∈ Õ ↔ ∃ g h : K, g ∈ B ∧ h ∈ B ∧ (∀ hh : h ∈ Õ, IsUnit (⟨h, hh⟩ : ↥Õ)) ∧ f * h = g)
    (O₀ : Subring K) (hO₀ : ∀ f : K, f ∈ O₀ ↔ f ∈ Õ ∧ ∀ σ : K ≃ₐ[k] K, σ ∈ G → σ f = f)

    (τ₀ : K ≃ₐ[k] K) (hτ₀G : τ₀ ∈ G) (hτ₀Õ : ∀ f : K, f ∈ Õ ↔ τ₀ f ∈ Õ) (n : ℕ) (hn : 1 ≤ n)
    (hτ₀n : ∀ f : K, (τ₀ ^ n) f = f)
    (hHcyc : ∀ σ : K ≃ₐ[k] K, σ ∈ G → (∀ f : K, f ∈ Õ ↔ σ f ∈ Õ) → ∃ j : ℕ, ∀ f : K, σ f = (τ₀ ^ j) f)

    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : maximalIdeal W = Ideal.span {π}) (m : ℕ) (hm : 1 ≤ m)
    [IsLocalRing (UVCrossingModel W (π ^ m))]
    [IsAdicComplete (maximalIdeal (UVCrossingModel W (π ^ m))) (UVCrossingModel W (π ^ m))]
    (hnW : IsUnit ((n : ℕ) : W)) (ζ ζ' : W) (hζ : ζ * ζ' = 1) (hζn : ζ ^ n = 1)
    (hζprim : ∀ j : ℕ, 0 < j → j < n → ζ ^ j ≠ 1)
    (ι : AdicCompletion (maximalIdeal ↥Õ) ↥Õ ≃+* UVCrossingModel W (π ^ m))
    (θ₀ : UVCrossingModel W (π ^ m) ≃ₐ[W] UVCrossingModel W (π ^ m))
    (htanU : θ₀ (U (π ^ m)) - const (π ^ m) ζ * U (π ^ m) ∈ maximalIdeal (UVCrossingModel W (π ^ m)) ^ 2)
    (htanV : θ₀ (V (π ^ m)) - const (π ^ m) ζ' * V (π ^ m) ∈ maximalIdeal (UVCrossingModel W (π ^ m)) ^ 2)
    (hequiv : ∀ (f : K) (hf : f ∈ Õ) (hf' : τ₀ f ∈ Õ),
      ι (algebraMap ↥Õ _ ⟨_, hf'⟩) = θ₀ (ι (algebraMap ↥Õ _ ⟨f, hf⟩)))

    {R₀ : Type*} [CommRing R₀] (cK : R₀ →+* K) (cW : R₀ →+* W) (hcO₀ : ∀ a : R₀, cK a ∈ O₀)
    (hconst : ∀ (a : R₀) (ha : cK a ∈ Õ), ι (algebraMap ↥Õ _ ⟨cK a, ha⟩) = const (π ^ m) (cW a)) :
    ∃ (_ : IsNoetherianRing ↥Õ) (_ : IsLocalRing ↥O₀) (_ : IsNoetherianRing ↥O₀) (hle : O₀ ≤ Õ)
      (κ : AdicCompletion (maximalIdeal ↥O₀) ↥O₀ →+* AdicCompletion (maximalIdeal ↥Õ) ↥Õ)
      (ι₀ : AdicCompletion (maximalIdeal ↥O₀) ↥O₀ ≃+* UVCrossingModel W (π ^ (m * n)))
      (ψ : UVCrossingModel W (π ^ (m * n)) →+* UVCrossingModel W (π ^ m))
      (γ : (UVCrossingModel W (π ^ m))ˣ),

      (∀ f : ↥O₀, IsUnit f ↔ IsUnit (Subring.inclusion hle f)) ∧

      (∀ f : ↥O₀, κ (algebraMap ↥O₀ _ f) = algebraMap ↥Õ _ (Subring.inclusion hle f)) ∧
      Function.Injective κ ∧
      (∀ x : AdicCompletion (maximalIdeal ↥Õ) ↥Õ, x ∈ Set.range κ ↔ θ₀ (ι x) = ι x) ∧

      Function.Injective ψ ∧
      (∀ w : W, ψ (const (π ^ (m * n)) w) = const (π ^ m) w) ∧
      (γ : UVCrossingModel W (π ^ m)) - 1 ∈ maximalIdeal (UVCrossingModel W (π ^ m)) ∧
      ψ (U (π ^ (m * n))) = ((γ : UVCrossingModel W (π ^ m)) * U (π ^ m)) ^ n ∧
      ψ (V (π ^ (m * n))) = ((↑γ⁻¹ : UVCrossingModel W (π ^ m)) * V (π ^ m)) ^ n ∧
      (∀ z : UVCrossingModel W (π ^ m), z ∈ Set.range ψ ↔ θ₀ z = z) ∧

      (∀ y : AdicCompletion (maximalIdeal ↥O₀) ↥O₀, ψ (ι₀ y) = ι (κ y)) ∧
      (∀ a : R₀, ι₀ (algebraMap ↥O₀ _ ⟨cK a, hcO₀ a⟩) = const (π ^ (m * n)) (cW a)) ∧
      (∀ z : UVCrossingModel W (π ^ m), θ₀^[n] z = z) := by
  classical

  let H : Subgroup (K ≃ₐ[k] K) :=
    { carrier := {σ | σ ∈ G ∧ ∀ f : K, f ∈ Õ ↔ σ f ∈ Õ}
      mul_mem' := fun {a b} ha hb => ⟨G.mul_mem ha.1 hb.1, fun f => by
        rw [AlgEquiv.mul_apply]; exact (hb.2 f).trans (ha.2 (b f))⟩
      one_mem' := ⟨G.one_mem, fun f => by rw [AlgEquiv.one_apply]⟩
      inv_mem' := fun {a} ha => ⟨G.inv_mem ha.1, fun f => by
        have h := (ha.2 (a⁻¹ f)).symm
        have e : a (a⁻¹ f) = f := by
          change a (a.symm f) = f
          exact a.apply_symm_apply f
        rwa [e] at h⟩ }
  have hH : ∀ σ : K ≃ₐ[k] K, σ ∈ H ↔ σ ∈ G ∧ ∀ f : K, f ∈ Õ ↔ σ f ∈ Õ := fun _ => Iff.rfl
  obtain ⟨hÕnoeth, hO₀loc, hO₀noeth, hle, act, κ, hunits, hact, hlev, huniq, hκinj, hκof, hrange⟩ :=
    IsLocalRing.exists_ringHom_adicCompletion_inf_fixedPoints_range_eq_of_isLocalization
      G hG B hBG BG hBGdef hBGnoeth hfin Õ hBÕ hloc H hH O₀ hO₀
  haveI := hÕnoeth
  haveI := hO₀loc
  haveI := hO₀noeth
  let τ : ↥H := ⟨τ₀, hτ₀G, hτ₀Õ⟩

  have act_one : act 1 = RingHom.id _ := by
    symm
    apply huniq 1 (RingHom.id _)
    · intro f
      refine ⟨by change (1 : K ≃ₐ[k] K) (f : K) ∈ Õ; rw [AlgEquiv.one_apply]; exact f.2, ?_⟩
      rw [RingHom.id_apply]
      rfl
    · intro n x hx; exact hx
  have act_mul : ∀ σ ρ : ↥H, act (σ * ρ) = (act σ).comp (act ρ) := by
    intro σ ρ
    symm
    apply huniq (σ * ρ) ((act σ).comp (act ρ))
    · intro f
      obtain ⟨h1, e1⟩ := hact ρ f
      obtain ⟨h2, e2⟩ := hact σ ⟨(ρ : K ≃ₐ[k] K) (f : K), h1⟩
      refine ⟨by change ((σ : K ≃ₐ[k] K) * (ρ : K ≃ₐ[k] K)) (f : K) ∈ Õ; rw [AlgEquiv.mul_apply]; exact h2, ?_⟩
      rw [RingHom.comp_apply, e1, e2]
      congr 1
    · intro n x hx
      rw [RingHom.comp_apply]
      exact hlev σ n _ (hlev ρ n x hx)
  have act_pow : ∀ (σ : ↥H) (j : ℕ), act (σ ^ j) = (act σ) ^ j := by
    intro σ j
    induction j with
    | zero => rw [pow_zero, pow_zero, act_one]; rfl
    | succ j ih => rw [pow_succ, act_mul, ih, pow_succ]; rfl

  have hsq : ∀ x : AdicCompletion (maximalIdeal ↥Õ) ↥Õ, ι (act τ x) = θ₀ (ι x) := by
    let F : AdicCompletion (maximalIdeal ↥Õ) ↥Õ ≃+* AdicCompletion (maximalIdeal ↥Õ) ↥Õ :=
      (ι.trans θ₀.toRingEquiv).trans ι.symm
    have hF : F.toRingHom = act τ := by
      apply huniq τ F.toRingHom
      · intro f
        refine ⟨(hτ₀Õ f).mp f.2, ?_⟩
        change ι.symm (θ₀ (ι (algebraMap ↥Õ _ f))) = _
        rw [← hequiv (f : K) f.2 ((hτ₀Õ f).mp f.2), RingEquiv.symm_apply_apply]
      · intro n x hx
        exact evalₐ_ringEquiv_eq_zero F n x hx
    intro x
    have : act τ x = ι.symm (θ₀ (ι x)) := by rw [← hF]; rfl
    rw [this, RingEquiv.apply_symm_apply]
  have hsq_iter : ∀ (j : ℕ) (x : AdicCompletion (maximalIdeal ↥Õ) ↥Õ), ι (((act τ) ^ j) x) = (θ₀^[j]) (ι x) := by
    intro j
    induction j with
    | zero => intro x; rfl
    | succ j ih =>
        intro x
        rw [pow_succ, RingHom.mul_def, RingHom.comp_apply, Function.iterate_succ_apply, ← hsq, ih]

  have hτn : τ ^ n = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact AlgEquiv.ext hτ₀n
  have hactn : (act τ) ^ n = RingHom.id _ := by rw [← act_pow, hτn, act_one]
  have hord : ∀ z : UVCrossingModel W (π ^ m), θ₀^[n] z = z := by
    intro z
    have := hsq_iter n (ι.symm z)
    rw [hactn, RingHom.id_apply, RingEquiv.apply_symm_apply] at this
    exact this.symm

  have hπmem : π ∈ maximalIdeal W := by rw [hπ]; exact Ideal.mem_span_singleton_self π
  have hπne : π ≠ 0 := by
    intro h0
    apply IsDiscreteValuationRing.not_a_field' (R := W)
    rw [hπ, h0, Ideal.span_singleton_eq_bot]
  have hπmu : ¬ IsUnit (π ^ m) := fun hu =>
    (IsLocalRing.mem_maximalIdeal _).mp hπmem (isUnit_pow_iff (by omega) |>.mp hu)
  have hπmnz : π ^ m ∈ nonZeroDivisors W := mem_nonZeroDivisors_of_ne_zero (pow_ne_zero m hπne)
  have hnil : ∃ j : ℕ, maximalIdeal W ^ j ≤ Ideal.span {π ^ m} := ⟨m, by rw [hπ, Ideal.span_singleton_pow]⟩
  have hreg : ∀ j : ℕ, 0 < j → j < n → ζ ^ j - 1 ∈ nonZeroDivisors W :=
    fun j hj hjn => mem_nonZeroDivisors_of_ne_zero (sub_ne_zero.mpr (hζprim j hj hjn))
  obtain ⟨ψ₀, γ, hψ₀inj, hfix, hγ, hψ₀U, hψ₀V⟩ :=
    ModularCurve.UVCrossingModel.exists_algHom_range_eq_fixedPoints_apply_U_apply_V_of_tangent
      (π ^ m) hπmu hπmnz hnil n hnW ζ ζ' hζ hζn hreg θ₀ hord htanU htanV

  have hpow : (π ^ m) ^ n = π ^ (m * n) := (pow_mul π m n).symm
  let cast : UVCrossingModel W ((π ^ m) ^ n) ≃+* UVCrossingModel W (π ^ (m * n)) :=
    Ideal.quotEquivOfEq (by rw [hpow])
  have cast_mk : ∀ p, cast (UVCrossingModel.mk ((π ^ m) ^ n) p) = UVCrossingModel.mk (π ^ (m * n)) p :=
    fun p => Ideal.quotEquivOfEq_mk _ _
  have cast_symm_mk : ∀ p, cast.symm (UVCrossingModel.mk (π ^ (m * n)) p) = UVCrossingModel.mk ((π ^ m) ^ n) p := by
    intro p; rw [← cast_mk, RingEquiv.symm_apply_apply]
  let ψ : UVCrossingModel W (π ^ (m * n)) →+* UVCrossingModel W (π ^ m) := ψ₀.toRingHom.comp cast.symm.toRingHom
  have ψ_apply : ∀ z, ψ z = ψ₀ (cast.symm z) := fun _ => rfl
  have hψinj : Function.Injective ψ := hψ₀inj.comp cast.symm.injective
  have hψconst : ∀ w : W, ψ (const (π ^ (m * n)) w) = const (π ^ m) w := by
    intro w
    rw [ψ_apply]
    change ψ₀ (cast.symm (UVCrossingModel.mk (π ^ (m * n)) (MvPowerSeries.C w))) = UVCrossingModel.mk (π ^ m) (MvPowerSeries.C w)
    rw [cast_symm_mk]
    have h1 : UVCrossingModel.mk ((π ^ m) ^ n) (MvPowerSeries.C w) = algebraMap W _ w := rfl
    have h2 : UVCrossingModel.mk (π ^ m) (MvPowerSeries.C w) = algebraMap W _ w := rfl
    rw [h1, h2, AlgHom.commutes]
  have hψU : ψ (U (π ^ (m * n))) = ((γ : UVCrossingModel W (π ^ m)) * U (π ^ m)) ^ n := by
    rw [ψ_apply]; change ψ₀ (cast.symm (UVCrossingModel.mk _ _)) = _; rw [cast_symm_mk]; exact hψ₀U
  have hψV : ψ (V (π ^ (m * n))) = ((↑γ⁻¹ : UVCrossingModel W (π ^ m)) * V (π ^ m)) ^ n := by
    rw [ψ_apply]; change ψ₀ (cast.symm (UVCrossingModel.mk _ _)) = _; rw [cast_symm_mk]; exact hψ₀V
  have hψrange : ∀ z, z ∈ Set.range ψ ↔ θ₀ z = z := by
    intro z
    rw [hfix]
    constructor
    · rintro ⟨y, rfl⟩; exact ⟨cast.symm y, rfl⟩
    · rintro ⟨y, rfl⟩; exact ⟨cast y, by rw [ψ_apply, RingEquiv.symm_apply_apply]⟩

  have hrangeθ : ∀ x : AdicCompletion (maximalIdeal ↥Õ) ↥Õ, x ∈ Set.range κ ↔ θ₀ (ι x) = ι x := by
    intro x
    rw [hrange]
    constructor
    · intro hx; rw [← hsq, hx τ]
    · intro hx σ
      obtain ⟨j, hj⟩ := hHcyc (σ : K ≃ₐ[k] K) σ.2.1 σ.2.2
      have hσ : σ = τ ^ j := by
        apply Subtype.ext; rw [Subgroup.coe_pow]; exact AlgEquiv.ext hj
      have hfix1 : act τ x = x := ι.injective (by rw [hsq, hx])
      rw [hσ, act_pow, RingHom.coe_pow]
      exact Function.iterate_fixed hfix1 j

  let Φ : AdicCompletion (maximalIdeal ↥O₀) ↥O₀ →+* UVCrossingModel W (π ^ m) := ι.toRingHom.comp κ
  have Φ_apply : ∀ y, Φ y = ι (κ y) := fun _ => rfl
  have hΦinj : Function.Injective Φ := ι.injective.comp hκinj
  have hrange_eq : Φ.range = ψ.range := by
    ext z
    rw [RingHom.mem_range, RingHom.mem_range]
    change z ∈ Set.range Φ ↔ z ∈ Set.range ψ
    rw [hψrange]
    constructor
    · rintro ⟨y, rfl⟩
      rw [Φ_apply, ← hsq]
      congr 1
      exact ((hrange (κ y)).mp ⟨y, rfl⟩) τ
    · intro hz
      have hx : ι.symm z ∈ Set.range κ := by rw [hrangeθ, RingEquiv.apply_symm_apply]; exact hz
      obtain ⟨y, hy⟩ := hx
      exact ⟨y, by rw [Φ_apply, hy, RingEquiv.apply_symm_apply]⟩
  let e₁ : AdicCompletion (maximalIdeal ↥O₀) ↥O₀ ≃+* Φ.range :=
    RingEquiv.ofBijective Φ.rangeRestrict ⟨fun a b h => hΦinj (congrArg Subtype.val h), RingHom.rangeRestrict_surjective Φ⟩
  let e₂ : UVCrossingModel W (π ^ (m * n)) ≃+* ψ.range :=
    RingEquiv.ofBijective ψ.rangeRestrict ⟨fun a b h => hψinj (congrArg Subtype.val h), RingHom.rangeRestrict_surjective ψ⟩
  let e₃ : Φ.range ≃+* ψ.range := RingEquiv.subringCongr hrange_eq
  let ι₀ : AdicCompletion (maximalIdeal ↥O₀) ↥O₀ ≃+* UVCrossingModel W (π ^ (m * n)) := e₁.trans (e₃.trans e₂.symm)
  have he₂ : ∀ y : ψ.range, ψ (e₂.symm y) = (y : UVCrossingModel W (π ^ m)) := by
    intro y
    have : (e₂ (e₂.symm y) : UVCrossingModel W (π ^ m)) = y := by rw [RingEquiv.apply_symm_apply]
    exact this
  have he₃ : ∀ y : Φ.range, (e₃ y : UVCrossingModel W (π ^ m)) = y := fun _ => rfl
  have he₁ : ∀ y, (e₁ y : UVCrossingModel W (π ^ m)) = Φ y := fun _ => rfl
  have hsquare : ∀ y, ψ (ι₀ y) = ι (κ y) := by
    intro y
    change ψ (e₂.symm (e₃ (e₁ y))) = ι (κ y)
    rw [he₂, he₃, he₁]
    rfl
  have hι₀const : ∀ a : R₀, ι₀ (algebraMap ↥O₀ _ ⟨cK a, hcO₀ a⟩) = const (π ^ (m * n)) (cW a) := by
    intro a
    apply hψinj
    rw [hsquare, hκof, hψconst]
    exact hconst a (hle (hcO₀ a))
  exact ⟨hÕnoeth, hO₀loc, hO₀noeth, hle, κ, ι₀, ψ, γ, hunits, hκof, hκinj, hrangeθ, hψinj, hψconst, hγ, hψU, hψV,
    hψrange, hsquare, hι₀const, hord⟩

theorem pernode_coords
    {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : maximalIdeal W = Ideal.span {π}) (w : ℕ) (hw : 1 ≤ w)
    {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    (ι : AdicCompletion (maximalIdeal O) O ≃+* UVCrossingModel W (π ^ w))
    (t : O) (ht : ι (algebraMap O (AdicCompletion (maximalIdeal O) O) t) = const (π ^ w) π)
    (𝔭x 𝔭t : Ideal O) [𝔭x.IsPrime] [𝔭t.IsPrime] (hne : 𝔭x ≠ 𝔭t)
    (htx : t ∈ 𝔭x) (htt : t ∈ 𝔭t) (hxm : 𝔭x ≠ maximalIdeal O) (htm : 𝔭t ≠ maximalIdeal O) :
    ∃ (ι' : AdicCompletion (maximalIdeal O) O ≃+* UVCrossingModel W (π ^ w)) (cx cy : O) (u : Oˣ)
      (γU γV : (UVCrossingModel W (π ^ w))ˣ),
      (∀ (x : AdicCompletion (maximalIdeal O) O) (c : W), ι x = const (π ^ w) c → ι' x = const (π ^ w) c) ∧
      ((∀ x : AdicCompletion (maximalIdeal O) O, ι' x = ι x) ∨
        (∀ x : AdicCompletion (maximalIdeal O) O, ι' x = crossingSwap (π ^ w) (ι x))) ∧
      ι' (algebraMap O (AdicCompletion (maximalIdeal O) O) cx) = (γU : UVCrossingModel W (π ^ w)) * U (π ^ w) ∧
      ι' (algebraMap O (AdicCompletion (maximalIdeal O) O) cy) = (γV : UVCrossingModel W (π ^ w)) * V (π ^ w) ∧
      cx * cy = t ^ w * (u : O) ∧
      maximalIdeal O = Ideal.span {cx, cy, t} ∧
      cx ∈ 𝔭x ∧ cx ∉ 𝔭t ∧ cy ∈ 𝔭t ∧ cy ∉ 𝔭x ∧
      (∀ f : O, f ∈ 𝔭x ↔ ι' (algebraMap O (AdicCompletion (maximalIdeal O) O) f) ∈ Ideal.span {const (π ^ w) π, U (π ^ w)}) ∧
      (∀ f : O, f ∈ 𝔭t ↔ ι' (algebraMap O (AdicCompletion (maximalIdeal O) O) f) ∈ Ideal.span {const (π ^ w) π, V (π ^ w)}) := by
  classical

  have hswU : crossingSwap (π ^ w) (U (π ^ w)) = V (π ^ w) := by
    change crossingSwap (π ^ w) (UVCrossingModel.mk (π ^ w) (MvPowerSeries.X 0)) = UVCrossingModel.mk (π ^ w) (MvPowerSeries.X 1)
    rw [crossingSwap_mk, uvSwapEquiv_X_zero]
  have hswV : crossingSwap (π ^ w) (V (π ^ w)) = U (π ^ w) := by
    change crossingSwap (π ^ w) (UVCrossingModel.mk (π ^ w) (MvPowerSeries.X 1)) = UVCrossingModel.mk (π ^ w) (MvPowerSeries.X 0)
    rw [crossingSwap_mk, uvSwapEquiv_X_one]
  have hswC : ∀ c : W, crossingSwap (π ^ w) (const (π ^ w) c) = const (π ^ w) c := by
    intro c
    change crossingSwap (π ^ w) (UVCrossingModel.mk (π ^ w) (MvPowerSeries.C c)) = UVCrossingModel.mk (π ^ w) (MvPowerSeries.C c)
    rw [crossingSwap_mk, uvSwapEquiv_C]

  have hmemmap : ∀ (e : UVCrossingModel W (π ^ w) ≃+* UVCrossingModel W (π ^ w)) (I : Ideal (UVCrossingModel W (π ^ w))) (z : UVCrossingModel W (π ^ w)),
      z ∈ I ↔ e z ∈ I.map e.toRingHom := by
    intro e I z
    constructor
    · intro hz; exact Ideal.mem_map_of_mem e.toRingHom hz
    · intro hz
      have h1 := Ideal.mem_map_of_mem e.symm.toRingHom hz
      rw [Ideal.map_map, RingEquiv.symm_toRingHom_comp_toRingHom, Ideal.map_id] at h1
      simpa using h1
  have hmapspan : ∀ (a b : UVCrossingModel W (π ^ w)),
      (Ideal.span {a, b}).map (crossingSwap (π ^ w)).toRingHom = Ideal.span {crossingSwap (π ^ w) a, crossingSwap (π ^ w) b} := by
    intro a b
    rw [Ideal.map_span, Set.image_pair]
    rfl

  have hbm := ModularCurve.UVCrossingModel.mem_iff_ringEquiv_adicCompletion_mem_span_or_swap_of_ne
    π hπ w hw ι t ht 𝔭x 𝔭t hne htx htt hxm htm
  obtain ⟨ι', hι'c, hι'rel, hι'x, hι't⟩ : ∃ (ι' : AdicCompletion (maximalIdeal O) O ≃+* UVCrossingModel W (π ^ w)),
      (∀ (x : AdicCompletion (maximalIdeal O) O) (c : W), ι x = const (π ^ w) c → ι' x = const (π ^ w) c) ∧
      ((∀ x : AdicCompletion (maximalIdeal O) O, ι' x = ι x) ∨
        (∀ x : AdicCompletion (maximalIdeal O) O, ι' x = crossingSwap (π ^ w) (ι x))) ∧
      (∀ f : O, f ∈ 𝔭x ↔ ι' (algebraMap O _ f) ∈ Ideal.span {const (π ^ w) π, U (π ^ w)}) ∧
      (∀ f : O, f ∈ 𝔭t ↔ ι' (algebraMap O _ f) ∈ Ideal.span {const (π ^ w) π, V (π ^ w)}) := by
    rcases hbm with ⟨hx, ht'⟩ | ⟨hx, ht'⟩
    · exact ⟨ι, fun x c h => h, Or.inl (fun x => rfl), hx, ht'⟩
    · refine ⟨ι.trans (crossingSwap (π ^ w)), fun x c h => ?_, Or.inr (fun x => rfl), fun f => ?_, fun f => ?_⟩
      · rw [RingEquiv.trans_apply, h, hswC]
      · rw [hx f, RingEquiv.trans_apply, hmemmap (crossingSwap (π ^ w)) (Ideal.span {const (π ^ w) π, V (π ^ w)}),
          hmapspan, hswC, hswV]
      · rw [ht' f, RingEquiv.trans_apply, hmemmap (crossingSwap (π ^ w)) (Ideal.span {const (π ^ w) π, U (π ^ w)}),
          hmapspan, hswC, hswU]
  have ht2 : ι' (algebraMap O (AdicCompletion (maximalIdeal O) O) t) = const (π ^ w) π := hι'c _ _ ht

  obtain ⟨xn, yn, u, γ, γ', hu, hγ, hγ', hxn, hyn, hxy, hmax⟩ :=
    ModularCurve.UVCrossingModel.exists_mul_eq_pow_mul_and_maximalIdeal_eq_span_of_ringEquiv_adicCompletion_pow
      π hπ w hw ι' t ht2 𝔭x 𝔭t hne htx htt hxm htm

  have hπc : const (π ^ w) π ∈ Ideal.span {const (π ^ w) π, U (π ^ w)} := Ideal.subset_span (by simp)
  have hxn_x : xn ∈ 𝔭x := by
    rw [hι'x, hxn]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  have hyn_t : yn ∈ 𝔭t := by
    rw [hι't, hyn]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  have hgen_le : ∀ (P : Ideal O), xn ∈ P → yn ∈ P → t ∈ P → maximalIdeal O ≤ P := by
    intro P h1 h2 h3
    rw [hmax, Ideal.span_le]
    rintro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
  have hxn_t : xn ∉ 𝔭t := by
    intro h
    apply htm
    exact le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) (hgen_le 𝔭t h hyn_t htt)
  have hyn_x : yn ∉ 𝔭x := by
    intro h
    apply hxm
    exact le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) (hgen_le 𝔭x hxn_x h htx)
  refine ⟨ι', xn, yn, hu.unit, hγ.unit, hγ'.unit, hι'c, hι'rel, ?_, ?_, ?_, hmax, hxn_x, hxn_t, hyn_t, hyn_x, hι'x, hι't⟩
  · rw [IsUnit.unit_spec]; exact hxn
  · rw [IsUnit.unit_spec]; exact hyn
  · rw [IsUnit.unit_spec]; exact hxy

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

section PartB

variable (G : Subgroup (K ≃ₐ[k] K))
  (B : Subring K) (hBG : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ f : K, f ∈ B → σ f ∈ B)
  (Õ : Subring K) [IsLocalRing ↥Õ] (hBÕ : B ≤ Õ)
  (hloc : ∀ f : K, f ∈ Õ ↔ ∃ g h : K, g ∈ B ∧ h ∈ B ∧ (∀ hh : h ∈ Õ, IsUnit (⟨h, hh⟩ : ↥Õ)) ∧ f * h = g)

include hBG hBÕ hloc

theorem exists_invariant_fraction [Finite ↥G] (f : K) (hfÕ : f ∈ Õ) (hfG : ∀ σ : ↥G, σ • f = f) :
    ∃ g h : K, g ∈ B ∧ h ∈ B ∧ (∀ σ : ↥G, σ • g = g) ∧ (∀ σ : ↥G, σ • h = h) ∧
      (∀ hh : h ∈ Õ, IsUnit (⟨h, hh⟩ : ↥Õ)) ∧ f * h = g := by
  classical
  haveI : Fintype ↥G := Fintype.ofFinite ↥G
  have hBG' : ∀ (σ : ↥G) (b : K), b ∈ B → σ • b ∈ B := fun σ b hb => hBG σ σ.2 b hb

  let I : Ideal ↥B :=
    { carrier := {h | f * (h : K) ∈ B}
      add_mem' := fun {a b} ha hb => by
        change f * ((a : K) + b) ∈ B
        rw [mul_add]; exact B.add_mem ha hb
      zero_mem' := by change f * (0 : K) ∈ B; rw [mul_zero]; exact B.zero_mem
      smul_mem' := fun c {a} ha => by
        change f * ((c : K) * a) ∈ B
        rw [mul_left_comm]; exact B.mul_mem c.2 ha }
  have memI : ∀ h : ↥B, h ∈ I ↔ f * (h : K) ∈ B := fun _ => Iff.rfl

  let φ : ↥G → (↥B →+* ↥Õ) := fun σ =>
    { toFun := fun b => ⟨σ • (b : K), hBÕ (hBG' σ _ b.2)⟩
      map_one' := Subtype.ext (by change σ • ((1 : ↥B) : K) = 1; rw [OneMemClass.coe_one, smul_one])
      map_mul' := fun a b => Subtype.ext (by change σ • ((a : K) * b) = σ • (a : K) * σ • (b : K); rw [smul_mul'])
      map_zero' := Subtype.ext (by change σ • ((0 : ↥B) : K) = 0; rw [ZeroMemClass.coe_zero, smul_zero])
      map_add' := fun a b => Subtype.ext (by change σ • ((a : K) + b) = σ • (a : K) + σ • (b : K); rw [smul_add]) }
  let Q : ↥G → Ideal ↥B := fun σ => Ideal.comap (φ σ) (IsLocalRing.maximalIdeal ↥Õ)
  have hQprime : ∀ σ, (Q σ).IsPrime := fun σ => Ideal.comap_isPrime (φ σ) _
  have memQ : ∀ (σ : ↥G) (b : ↥B), b ∈ Q σ ↔ (⟨σ • (b : K), hBÕ (hBG' σ _ b.2)⟩ : ↥Õ) ∈ IsLocalRing.maximalIdeal ↥Õ :=
    fun _ _ => Iff.rfl

  obtain ⟨g₁, h₁, hg₁B, hh₁B, hh₁u, hfh₁⟩ := (hloc f).mp hfÕ
  have hnot : ∀ σ : ↥G, ¬ (I ≤ Q σ) := by
    intro σ hle
    have hmem : (⟨σ⁻¹ • h₁, hBG' _ _ hh₁B⟩ : ↥B) ∈ I := by
      rw [memI]
      change f * (σ⁻¹ • h₁) ∈ B
      have : f * (σ⁻¹ • h₁) = σ⁻¹ • (f * h₁) := by rw [smul_mul', hfG σ⁻¹]
      rw [this, hfh₁]; exact hBG' _ _ hg₁B
    have h2 := hle hmem
    rw [memQ] at h2
    apply (IsLocalRing.mem_maximalIdeal _).mp ?_ (hh₁u (hBÕ hh₁B))
    have e : (⟨σ • ((⟨σ⁻¹ • h₁, hBG' _ _ hh₁B⟩ : ↥B) : K), hBÕ (hBG' σ _ (hBG' _ _ hh₁B))⟩ : ↥Õ) = ⟨h₁, hBÕ hh₁B⟩ := by
      apply Subtype.ext; change σ • σ⁻¹ • h₁ = h₁; rw [smul_inv_smul]
    rw [← e]; exact h2

  have havoid : ¬ ((I : Set ↥B) ⊆ ⋃ σ ∈ (↑(Finset.univ : Finset ↥G) : Set ↥G), ((Q σ) : Set ↥B)) := by
    rw [Ideal.subset_union_prime (1 : ↥G) (1 : ↥G) (fun σ _ _ _ => hQprime σ)]
    rintro ⟨σ, -, hle⟩
    exact hnot σ hle
  rw [Set.not_subset] at havoid
  obtain ⟨h, hhI, hhQ⟩ := havoid
  have hhQ' : ∀ σ : ↥G, h ∉ Q σ := by
    intro σ hσ
    apply hhQ
    rw [Set.mem_iUnion₂]
    exact ⟨σ, Finset.mem_coe.mpr (Finset.mem_univ σ), hσ⟩
  have hfhB : f * (h : K) ∈ B := (memI h).mp hhI

  have hσhB : ∀ σ : ↥G, σ • (h : K) ∈ B := fun σ => hBG' σ _ h.2
  have hσhu : ∀ σ : ↥G, (⟨σ • (h : K), hBÕ (hσhB σ)⟩ : ↥Õ) ∉ IsLocalRing.maximalIdeal ↥Õ :=
    fun σ hσ => hhQ' σ ((memQ σ h).mpr hσ)
  set hp : K := ∏ σ : ↥G, σ • (h : K) with hhp
  have hp_B : hp ∈ B := Subring.prod_mem B (fun σ _ => hσhB σ)
  have hp_Õ : hp ∈ Õ := hBÕ hp_B
  have hpÕ_eq : ∀ hh : hp ∈ Õ, (⟨hp, hh⟩ : ↥Õ) = ∏ σ : ↥G, (⟨σ • (h : K), hBÕ (hσhB σ)⟩ : ↥Õ) := by
    intro hh
    apply Subtype.ext
    change hp = Õ.subtype (∏ σ : ↥G, (⟨σ • (h : K), hBÕ (hσhB σ)⟩ : ↥Õ))
    rw [map_prod, hhp]
    rfl
  have hp_unit : ∀ hh : hp ∈ Õ, IsUnit (⟨hp, hh⟩ : ↥Õ) := by
    intro hh
    rw [hpÕ_eq hh]
    apply Finset.prod_induction (p := fun x : ↥Õ => IsUnit x)
    · intro a b ha hb; exact ha.mul hb
    · exact isUnit_one
    · intro σ _
      have := hσhu σ
      rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at this
  have hpG : ∀ τ : ↥G, τ • hp = hp := by
    intro τ
    rw [hhp, Finset.smul_prod']
    simp_rw [smul_smul]
    exact Fintype.prod_equiv (Equiv.mulLeft τ) _ _ (fun σ => rfl)
  have hg'B : f * hp ∈ B := by
    have : hp = (h : K) * ∏ σ ∈ (Finset.univ : Finset ↥G).erase 1, σ • (h : K) := by
      rw [hhp, ← Finset.mul_prod_erase (Finset.univ : Finset ↥G) (fun σ => σ • (h : K)) (Finset.mem_univ 1), one_smul]
    rw [this, ← mul_assoc]
    exact B.mul_mem hfhB (Subring.prod_mem B (fun σ _ => hσhB σ))
  refine ⟨f * hp, hp, hg'B, hp_B, fun σ => ?_, hpG, hp_unit, rfl⟩
  rw [smul_mul', hfG, hpG]

end PartB

theorem mem_iff_exists_frac_invariant
    (G : Subgroup (K ≃ₐ[k] K)) (hG : Finite ↥G)
    (B : Subring K) (hBG : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ f : K, f ∈ B → σ f ∈ B)
    (BG : Subring K) (hBGdef : ∀ f : K, f ∈ BG ↔ f ∈ B ∧ ∀ σ : K ≃ₐ[k] K, σ ∈ G → σ f = f)
    (Õ : Subring K) [IsLocalRing ↥Õ] (hBÕ : B ≤ Õ)
    (hloc : ∀ f : K, f ∈ Õ ↔ ∃ g h : K, g ∈ B ∧ h ∈ B ∧ (∀ hh : h ∈ Õ, IsUnit (⟨h, hh⟩ : ↥Õ)) ∧ f * h = g)
    (O₀ : Subring K) (hO₀ : ∀ f : K, f ∈ O₀ ↔ f ∈ Õ ∧ ∀ σ : K ≃ₐ[k] K, σ ∈ G → σ f = f) :
    BG ≤ O₀ ∧ (∀ f : ↥O₀, IsUnit f ↔ IsUnit (⟨(f : K), ((hO₀ f).mp f.2).1⟩ : ↥Õ)) ∧
    ∀ f : K, f ∈ O₀ ↔ ∃ g h : K, g ∈ BG ∧ h ∈ BG ∧ (∀ hh : h ∈ O₀, IsUnit (⟨h, hh⟩ : ↥O₀)) ∧ f * h = g := by
  classical
  haveI : Finite ↥G := hG
  have hle : O₀ ≤ Õ := fun f hf => ((hO₀ f).mp hf).1
  have hBGB : BG ≤ B := fun f hf => ((hBGdef f).mp hf).1
  have hBGO₀ : BG ≤ O₀ := fun f hf => (hO₀ f).mpr ⟨hBÕ (hBGB hf), ((hBGdef f).mp hf).2⟩

  have hunits : ∀ f : ↥O₀, IsUnit f ↔ IsUnit (⟨(f : K), hle f.2⟩ : ↥Õ) := by
    intro f
    constructor
    · intro h; exact h.map (Subring.inclusion hle)
    · intro h
      obtain ⟨u, hu⟩ := h
      set g : ↥Õ := ↑u⁻¹ with hg
      have hfg : (f : K) * (g : K) = 1 := by
        have := congrArg (fun z : ↥Õ => (z : K)) u.mul_inv
        rw [hu] at this
        simpa using this
      have hf0 : (f : K) ≠ 0 := fun h0 => by rw [h0, zero_mul] at hfg; exact zero_ne_one hfg
      have hgeq : (g : K) = (f : K)⁻¹ := by
        calc (g : K) = (f : K)⁻¹ * ((f : K) * (g : K)) := by rw [← mul_assoc, inv_mul_cancel₀ hf0, one_mul]
          _ = (f : K)⁻¹ := by rw [hfg, mul_one]
      have hginv : ∀ σ : K ≃ₐ[k] K, σ ∈ G → σ (g : K) = (g : K) := by
        intro σ hσ
        rw [hgeq, map_inv₀, ((hO₀ f).mp f.2).2 σ hσ]
      have hgO₀ : (g : K) ∈ O₀ := (hO₀ _).mpr ⟨g.2, hginv⟩
      refine isUnit_iff_exists_inv.mpr ⟨⟨(g : K), hgO₀⟩, Subtype.ext ?_⟩
      simpa using hfg
  refine ⟨hBGO₀, hunits, fun f => ?_⟩
  constructor
  · intro hf
    obtain ⟨g, h, hgB, hhB, hgG, hhG, hhu, e⟩ :=
      exists_invariant_fraction G B hBG Õ hBÕ hloc f (hle hf) (fun σ => ((hO₀ f).mp hf).2 σ σ.2)
    refine ⟨g, h, (hBGdef g).mpr ⟨hgB, fun σ hσ => hgG ⟨σ, hσ⟩⟩, (hBGdef h).mpr ⟨hhB, fun σ hσ => hhG ⟨σ, hσ⟩⟩,
      fun hh => (hunits ⟨h, hh⟩).mpr (hhu (hle hh)), e⟩
  · rintro ⟨g, h, hg, hh, hhu, e⟩
    obtain ⟨u, hu⟩ := hhu (hBGO₀ hh)
    have hinv : (((u⁻¹ : (↥O₀)ˣ) : ↥O₀) : K) * h = 1 := by
      have := congrArg (fun z : ↥O₀ => (z : K)) u.inv_mul
      rw [hu] at this; exact this
    have : f = g * (((u⁻¹ : (↥O₀)ˣ) : ↥O₀) : K) := by
      calc f = f * ((((u⁻¹ : (↥O₀)ˣ) : ↥O₀) : K) * h) := by rw [hinv, mul_one]
        _ = (f * h) * (((u⁻¹ : (↥O₀)ˣ) : ↥O₀) : K) := by ring
        _ = g * (((u⁻¹ : (↥O₀)ˣ) : ↥O₀) : K) := by rw [e]
    rw [this]
    exact O₀.mul_mem (hBGO₀ hg) ((u⁻¹ : (↥O₀)ˣ) : ↥O₀).2

theorem maximalIdeal_comap_eq_span_singleton
    {K F : Type*} [Field K] [Field F] (W : ValuationSubring K) (ι : F →+* K) (t : F) (ht : ι t ∈ W)
    (hW : maximalIdeal ↥W = Ideal.span {(⟨ι t, ht⟩ : ↥W)}) :
    ∃ ht' : t ∈ W.comap ι, maximalIdeal ↥(W.comap ι) = Ideal.span {(⟨t, ht'⟩ : ↥(W.comap ι))} := by
  classical
  have ht' : t ∈ W.comap ι := by rw [ValuationSubring.mem_comap]; exact ht
  refine ⟨ht', ?_⟩

  let φ : ↥(W.comap ι) →+* ↥W :=
    { toFun := fun x => ⟨ι x, (ValuationSubring.mem_comap.mp x.2)⟩
      map_one' := Subtype.ext (by change ι 1 = 1; exact map_one ι)
      map_mul' := fun a b => Subtype.ext (by change ι (a * b) = ι a * ι b; exact map_mul ι _ _)
      map_zero' := Subtype.ext (by change ι 0 = 0; exact map_zero ι)
      map_add' := fun a b => Subtype.ext (by change ι (a + b) = ι a + ι b; exact map_add ι _ _) }
  have hφ : ∀ x : ↥(W.comap ι), (φ x : K) = ι x := fun _ => rfl

  have hunit : ∀ x : ↥(W.comap ι), IsUnit x ↔ IsUnit (φ x) := by
    intro x
    constructor
    · intro h; exact h.map φ
    · intro h
      have hx0 : (x : F) ≠ 0 := by
        intro h0
        have : φ x = 0 := Subtype.ext (by rw [hφ, h0, map_zero]; rfl)
        rw [this] at h
        exact not_isUnit_zero h

      obtain ⟨u, hu⟩ := h
      have hinvW : (ι x)⁻¹ ∈ W := by
        have e : ((u⁻¹ : (↥W)ˣ) : ↥W).val * ι x = 1 := by
          have := congrArg (fun z : ↥W => (z : K)) u.inv_mul
          rw [hu] at this; exact this
        have : (ι x)⁻¹ = ((u⁻¹ : (↥W)ˣ) : ↥W).val := (eq_inv_of_mul_eq_one_left e).symm
        rw [this]; exact ((u⁻¹ : (↥W)ˣ) : ↥W).2
      have hinv : (x : F)⁻¹ ∈ W.comap ι := by
        rw [ValuationSubring.mem_comap, map_inv₀]; exact hinvW
      exact isUnit_iff_exists_inv.mpr ⟨⟨(x : F)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩
  apply le_antisymm
  · intro f hf
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit] at hf
    have hfW : φ f ∈ maximalIdeal ↥W := (IsLocalRing.mem_maximalIdeal _).mpr hf
    rw [hW, Ideal.mem_span_singleton'] at hfW
    obtain ⟨g, hg⟩ := hfW
    have hgK : (g : K) * ι t = ι f := congrArg Subtype.val hg
    rw [Ideal.mem_span_singleton']
    by_cases ht0 : t = 0
    · refine ⟨0, Subtype.ext ?_⟩
      change (0 : F) * t = f
      have : ι f = 0 := by rw [← hgK, ht0, map_zero, mul_zero]
      rw [zero_mul]
      exact ((map_eq_zero_iff ι ι.injective).mp this).symm
    · have hg' : (g : K) = ι (f * t⁻¹) := by
        rw [map_mul, map_inv₀, ← hgK, mul_inv_cancel_right₀ ((map_ne_zero_iff ι ι.injective).mpr ht0)]
      have hmem : (f : F) * t⁻¹ ∈ W.comap ι := by
        rw [ValuationSubring.mem_comap, ← hg']; exact g.2
      refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
      change (f : F) * t⁻¹ * t = f
      rw [inv_mul_cancel_right₀ ht0]
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit]
    intro hu
    have : (⟨ι t, ht⟩ : ↥W) ∈ maximalIdeal ↥W := by rw [hW]; exact Ideal.mem_span_singleton_self _
    exact (IsLocalRing.mem_maximalIdeal _).mp this hu

end S3C4Pernode

attribute [local instance 10000] SubalgebraClass.toAlgebra Algebra.toSMul Algebra.toModule

open S3C4Pernode in

theorem solution
    (q : ℕ)
    [Fact q.Prime]
    (hq3 : q = 3)
    (M' : ℕ)
    [NeZero M']

    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (s : ↥W)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (π₀ : ↥k₀)
    (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (ℓ : ℕ)
    (ζ₀ : ↥k₀)
    (ϖt : ↥k₀)
    (Kb : IntermediateField ↥k₀ (AlgebraicClosure ℚ))
    (Ab : ValuationSubring ↥Kb)
    (hAb : ∀ x : ↥Kb, x ∈ Ab ↔ (x : (AlgebraicClosure ℚ)) ∈ A)
    (ϖb : ↥Ab)
    (ξ : ↥k₀)
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (Kℓ : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ]
    [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥Kℓ]
    (jℓ : ↥Kℓ)
    [Fact (jℓ ≠ 0)]
    (ϖt' : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (y : Ideal ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ))
    (Bt : Subalgebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)
    (Wt : ValuationSubring ↥Kℓ)
    (hBW : ∀ f : ↥Kℓ, f ∈ Bt → f ∈ Wt)
    (n : ℕ)
    (γ₀ : SL(2, ℤ))
    (τ₀ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ)
    (m : ℕ)
    (ζc : (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hjK : ModularCurve.jqNModC ↥k₀ q ∈ Kℓ)
    (a₀ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (ends : Finset (Subring ↥Kℓ))
    (hqM' : ¬ q ∣ M')
    (hA : A.LiesOverPrime q)
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
        ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
          ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
            coeffMap (IsLocalRing.residue ↥A) y)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
        Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)
    (hℓ : ℓ.Prime)
    (hℓ3 : 3 ≤ ℓ)
    (hℓq : ℓ ≠ q)
    (hℓM' : ¬ ℓ ∣ M')
    (hζ₀ : IsPrimitiveRoot ((ζ₀ : ↥k₀) : AlgebraicClosure ℚ) (q * ℓ))
    (hϖtA : (ϖt : AlgebraicClosure ℚ) ∈ A)
    (hϖt : ∃ u : ↥A, IsUnit u ∧ (ϖt : AlgebraicClosure ℚ) ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ) * (u : AlgebraicClosure ℚ))
    (hKb : Kb = ⊥)
    (hϖb : maximalIdeal ↥Ab = Ideal.span {ϖb})
    (hϖb0 : ϖb ≠ 0)
    (htame : IsUnit ((ℓg - 1 : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hξ : IsPrimitiveRoot ξ q)
    (hKℓ : Kℓ = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (hjℓ : ((jℓ : LaurentSeries ↥k₀)) = ModularCurve.coeffEmb ↥k₀ ModularCurve.jq)
    (hϖt' : (ϖt' : ↥k₀) = ϖt)
    (hy : y.IsMaximal)
    (hϖy : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ⟨π₀, hπ⟩ ∈ y)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
        (φ : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) →+* Ω), RingHom.ker φ = y → φ (jChartFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ∈ ModularCurve.ssJSet q Ω)
    (hover : (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
        (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
        (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
            ↥(modularFunctionFieldBar M'))) →
        (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        ∀ (hgK : (coeffEmb ↥k₀ g) ∈ Kℓ)
          (hgC : (⟨_, hgK⟩ : ↥Kℓ) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ),
        ∀ (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A),
          residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
          (⟨⟨_, hgK⟩, hgC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) -
              algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ⟨c, hc⟩ ∈ y))
    (hOrbit : ∀ y' : Ideal ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), y'.IsMaximal →
        algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ⟨π₀, hπ⟩ ∈ y' →
          (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
            (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
            (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
              0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
              0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
                ↥(modularFunctionFieldBar M'))) →
            (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
            ∀ (hgK : (coeffEmb ↥k₀ g) ∈ Kℓ)
              (hgC : (⟨_, hgK⟩ : ↥Kℓ) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ),
            ∀ (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A),
              residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
                (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
              (⟨⟨_, hgK⟩, hgC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) -
                  algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ⟨c, hc⟩ ∈ y') →
        ∃ (γ : SL(2, ℤ)) (_ : γ ∈ CongruenceSubgroup.Gamma q) (_ : γ ∈ CongruenceSubgroup.Gamma0 M')
          (τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ),
          ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ ∧
          (∀ f : ↥Kℓ, f ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ →
            τ f ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ∧
          (∀ (f : ↥Kℓ) (hf : f ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)
            (hf' : τ f ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ),
            (⟨f, hf⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) ∈ y ↔ (⟨τ f, hf'⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) ∈ y'))
    (hS1 :
        chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ ≤ Bt ∧
        (∀ f : ↥Kℓ, ∃ g h : ↥Bt, (h : ↥Kℓ) ≠ 0 ∧ f * (h : ↥Kℓ) = (g : ↥Kℓ)) ∧

        Algebra.FormallySmooth ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt ∧ Algebra.FinitePresentation ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt ∧
        Ring.KrullDimLE 1 (↥Bt ⧸ Ideal.span {algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt ⟨π₀, hπ⟩}) ∧

        (∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ Wt ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x) ∧
        maximalIdeal ↥Wt = Ideal.span {(⟨algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩, hBW _ (Bt.algebraMap_mem ⟨π₀, hπ⟩)⟩ : ↥Wt)} ∧
        IsDiscreteValuationRing ↥Wt ∧
        (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), b ∈ y ↔
          ∃ hb : (b : ↥Kℓ) ∈ Wt, (⟨(b : ↥Kℓ), hb⟩ : ↥Wt) ∈ maximalIdeal ↥Wt) ∧
        (∀ f : ↥Kℓ, f ∈ Wt ↔ ∃ g h : ↥Bt, (⟨(h : ↥Kℓ), hBW _ h.2⟩ : ↥Wt) ∉ maximalIdeal ↥Wt ∧ f * (h : ↥Kℓ) = (g : ↥Kℓ)) ∧

        (∀ (inst : Algebra (GaloisField q 2) (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))),
          ∃ (ρ : ↥Bt →+* DrinfeldCurve.CoordRing q (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))),
            Function.Surjective ρ ∧
            (∀ b : ↥Bt, ρ b = 0 ↔ (⟨(b : ↥Kℓ), hBW _ b.2⟩ : ↥Wt) ∈ maximalIdeal ↥Wt) ∧
            (∀ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), ρ (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt a) = algebraMap (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (DrinfeldCurve.CoordRing q (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))) (residue ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) a)) ∧
            (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
              ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
                (∀ f : ↥Kℓ, f ∈ Wt ↔ τ f ∈ Wt) →
                ∃ (c : (GaloisField q 2)ˣ) (hmem : (ModularCurve.FullLevel.redQ q γ, c) ∈ DrinfeldCurve.hSubgroup q),
                  (∀ (b : ↥Bt) (hb : τ (b : ↥Kℓ) ∈ Bt), ρ ⟨τ (b : ↥Kℓ), hb⟩ = DrinfeldCurve.hAction q (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨_, hmem⟩ (ρ b)) ∧
                  (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥Kℓ, τ k = k) → c ≠ 1) ∧

                  (∃ (γ' : SL(2, ℤ)) (_ : γ' ∈ CongruenceSubgroup.Gamma q) (_ : γ' ∈ CongruenceSubgroup.Gamma0 M') (τ' : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ)
                      (_ : ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ'⁻¹ Kℓ τ') (_ : ∀ f : ↥Kℓ, f ∈ Wt ↔ τ' f ∈ Wt)
                      (hmem' : ((1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)), c) ∈ DrinfeldCurve.hSubgroup q),
                    ∀ (b : ↥Bt) (hb : τ' (b : ↥Kℓ) ∈ Bt), ρ ⟨τ' (b : ↥Kℓ), hb⟩ = DrinfeldCurve.hAction q (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨_, hmem'⟩ (ρ b)))) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
            ∀ f : ↥Kℓ, f ∈ Bt → τ f ∈ Bt) ∧
        (∀ Q : Ideal ↥Bt, Q.IsPrime → algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt ⟨π₀, hπ⟩ ∈ Q →
          ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
            ∃ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ ∧
              ∀ b : ↥Bt, (⟨(b : ↥Kℓ), hBW _ b.2⟩ : ↥Wt) ∈ maximalIdeal ↥Wt → τ (b : ↥Kℓ) ∈ Bt ∧ ∀ hb : τ (b : ↥Kℓ) ∈ Bt, (⟨τ (b : ↥Kℓ), hb⟩ : ↥Bt) ∈ Q) ∧
        (∀ b : ↥Bt, (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
            ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
              ∀ hb : τ (b : ↥Kℓ) ∈ Bt, (⟨τ (b : ↥Kℓ), hBW _ hb⟩ : ↥Wt) ∈ maximalIdeal ↥Wt) →
          algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt ⟨π₀, hπ⟩ ∣ b))
    (hn1 : 1 ≤ n)
    (hnq : n ∣ q + 1)
    (hγ₀Γ : γ₀ ∈ CongruenceSubgroup.Gamma q)
    (hγ₀Γ0 : γ₀ ∈ CongruenceSubgroup.Gamma0 M')
    (hτ₀ : ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ₀⁻¹ Kℓ τ₀)
    (hτ₀W : ∀ f : ↥Kℓ, f ∈ Wt ↔ τ₀ f ∈ Wt)
    (hm1 : 1 ≤ m)
    (hm : ∃ w : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), IsUnit w ∧ ⟨π₀, hπ⟩ ^ m = ϖt' * w)
    (hζc : ζc ^ n = 1)
    (hζcprim : ∀ k : ℕ, 0 < k → k < n → IsUnit (ζc ^ k - 1))
    (hjC : (⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) ∈ chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)
    (ha₀y : (⟨(⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ), hjC⟩ : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) a₀ ∈ y)
    (hR7 : (∀ f : ↥Kℓ, f ∈ Bt → (τ₀ ^ n) f = f) ∧
          (∀ k : ℕ, 0 < k → k < n → ∃ f : ↥Kℓ, f ∈ Bt ∧ (τ₀ ^ k) f ≠ f) ∧
          (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
            ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
              (∀ f : ↥Kℓ, f ∈ Wt ↔ τ f ∈ Wt) → ∃ k : ℕ, k < n ∧ ∀ f : ↥Kℓ, f ∈ Bt → τ f = (τ₀ ^ k) f) ∧
          ends.card = q + 1 ∧
          (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
            ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
              (∀ f : ↥Kℓ, f ∈ Wt ↔ τ f ∈ Wt) → ∀ O ∈ ends, ∃ O' ∈ ends, ∀ f : ↥Kℓ, f ∈ O ↔ τ f ∈ O') ∧
          (∀ O ∈ ends, ∀ O' ∈ ends, ∃ (γ : SL(2, ℤ)) (_ : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ) (_ : ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ),
            (∀ f : ↥Kℓ, f ∈ Wt ↔ τ f ∈ Wt) ∧ ∀ f : ↥Kℓ, f ∈ O ↔ τ f ∈ O') ∧
          (∀ O ∈ ends, ∀ f : ↥Kℓ, f ∈ O ↔ τ₀ f ∈ O) ∧
          (∀ O ∈ ends, ∀ O' ∈ ends, O ≠ O' → ∃ (f : ↥Kℓ) (hf : f ∈ O) (hf' : f ∈ O'),
            ¬ IsUnit (⟨f, hf⟩ : ↥O) ∧ IsUnit (⟨f, hf'⟩ : ↥O')) ∧

          (∃ Bc : Subalgebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ, Algebra.FiniteType ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bc ∧
            (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
              ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
                ∀ f : ↥Kℓ, f ∈ Bc → τ f ∈ Bc) ∧
            ∀ O ∈ ends, (∀ f : ↥Kℓ, f ∈ Bc → f ∈ O) ∧
              (∀ f : ↥Kℓ, f ∈ O ↔ ∃ g h : ↥Kℓ, g ∈ Bc ∧ h ∈ Bc ∧ (∀ hh : h ∈ O, IsUnit (⟨h, hh⟩ : ↥O)) ∧ f * h = g)) ∧

          (∀ O ∈ ends, ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
              ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
                (∀ f : ↥Kℓ, f ∈ O → τ f ∈ Wt) → ∀ f : ↥Kℓ, f ∈ Wt ↔ τ f ∈ Wt) ∧
          (∀ O ∈ ends,

            (∀ f : ↥Kℓ, f ∈ O → f ∈ Wt) ∧ ∃ (_ : IsLocalRing ↥O) (_ : IsNoetherianRing ↥O),
            (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (b : ↥Kℓ) ∈ O) ∧
            (∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ O ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x) ∧
            (∀ (f : ↥Kℓ) (hf : f ∈ O), ∃ (a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (ha : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a ∈ O), ¬ IsUnit ((⟨f, hf⟩ : ↥O) - ⟨_, ha⟩)) ∧

            (∃ (hϖO : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ ∈ O) (cx cy : ↥O) (u : (↥O)ˣ) (ι : (AdicCompletion (maximalIdeal ↥O) ↥O) ≃+* (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m)))
               (γU γV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))ˣ) (θ₀ : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m)) ≃ₐ[(AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))] (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))) (ζc' : (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))) (_ : ζc * ζc' = 1)
               (_ : IsLocalRing (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))),
              cx * cy = (⟨_, hϖO⟩ : ↥O) ^ m * (u : ↥O) ∧
              (∀ (a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (ha : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a ∈ O), ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, ha⟩) = UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m) (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) a)) ∧
              ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cx) = (γU : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))) * UVCrossingModel.U ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m) ∧
              ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cy) = (γV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))) * UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m) ∧
              (∀ hcy : (cy : ↥Kℓ) ∈ Wt, (⟨(cy : ↥Kℓ), hcy⟩ : ↥Wt) ∈ maximalIdeal ↥Wt) ∧
              (∀ hcx : (cx : ↥Kℓ) ∈ Wt, (⟨(cx : ↥Kℓ), hcx⟩ : ↥Wt) ∉ maximalIdeal ↥Wt) ∧

              (∃ (hjaO : (⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a₀ ∈ O) (e : ℕ) (wV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))ˣ), 1 ≤ e ∧
                ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨(⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a₀, hjaO⟩) =
                  (wV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))) * (UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m)) ^ e) ∧
              (∀ (f : ↥Kℓ) (hf : f ∈ O) (hf' : τ₀ f ∈ O),
                ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, hf'⟩) = θ₀ (ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨f, hf⟩))) ∧
              θ₀ (UVCrossingModel.U ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m)) - UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m) ζc * UVCrossingModel.U ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m) ∈
                (maximalIdeal (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))) ^ 2 ∧
              θ₀ (UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m)) - UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m) ζc' * UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m) ∈
                (maximalIdeal (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))) ^ 2 ∧

              (∃ Wx : ValuationSubring ↥Kℓ,
                (∀ f : ↥Kℓ, f ∈ O → f ∈ Wx) ∧
                (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (b : ↥Kℓ) ∈ Wx) ∧
                (∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ Wx ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x) ∧
                IsDiscreteValuationRing ↥Wx ∧
                (∃ hϖWx : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ ∈ Wx, maximalIdeal ↥Wx = Ideal.span {(⟨_, hϖWx⟩ : ↥Wx)}) ∧
                (∃ (t : ↥Wx), ∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))),
                  (∃ hm : Polynomial.aeval (t : ↥Kℓ) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)) ∈ Wx, (⟨_, hm⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
                    ∀ i, p.coeff i ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∧

                (∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))),
                  (∃ hm : Polynomial.aeval (⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)) ∈ Wx, (⟨_, hm⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
                    ∀ i, p.coeff i ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∧
                (∀ hcx : (cx : ↥Kℓ) ∈ Wx, (⟨(cx : ↥Kℓ), hcx⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) ∧
                (∀ hcy : (cy : ↥Kℓ) ∈ Wx, (⟨(cy : ↥Kℓ), hcy⟩ : ↥Wx) ∉ maximalIdeal ↥Wx) ∧
                (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (∀ hb : (b : ↥Kℓ) ∈ Wx, (⟨(b : ↥Kℓ), hb⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) → b ∈ y) ∧
                (∃ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), b ∈ y ∧ ∀ hb : (b : ↥Kℓ) ∈ Wx, (⟨(b : ↥Kℓ), hb⟩ : ↥Wx) ∉ maximalIdeal ↥Wx) ∧

                (∀ O' ∈ ends, O' ≠ O → ∃ f : ↥Kℓ, f ∈ O' ∧ f ∉ Wx) ∧

                (∀ O' ∈ ends, ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
                  ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
                    (∀ f : ↥Kℓ, f ∈ O' → τ f ∈ Wx) → O' = O)) ∧

              (∃ Bx : Subalgebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ,
                (∀ f : ↥Kℓ, f ∈ Bx → f ∈ Bt ∧ f ∈ O) ∧
                Algebra.FiniteType ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bx ∧
                (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
                  ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
                    ∀ f : ↥Kℓ, f ∈ Bx → τ f ∈ Bx) ∧
                (∀ f : ↥Kℓ, f ∈ Bx → ∀ P : AlgebraicCurve.Place ↥k₀ ↥Kℓ, 0 ≤ P.ord jℓ → 0 ≤ P.ord f) ∧
                (∀ f : ↥Kℓ, f ∈ O ↔ ∃ g h : ↥Kℓ, g ∈ Bx ∧ h ∈ Bx ∧ (∀ hh : h ∈ O, IsUnit (⟨h, hh⟩ : ↥O)) ∧ f * h = g) ∧

                (∃ b : ↥Kℓ, b ∈ Bx ∧ ∀ V : ValuationSubring ↥Kℓ, (∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ V ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x) →
                  (∀ hϖV : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ ∈ V, (⟨algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩, hϖV⟩ : ↥V) ∈ maximalIdeal ↥V) →
                  (∀ hjV : (jℓ : ↥Kℓ) ∈ V, (∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), p.Monic →
                      ∀ hp : Polynomial.aeval (jℓ : ↥Kℓ) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)) ∈ V,
                        (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) →
                    (∃ f : ↥Kℓ, f ∈ O ∧ f ∉ V) → b ∉ V))))) ∧

          (∀ V : ValuationSubring ↥Kℓ, (∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ V ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x) →
            (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (b : ↥Kℓ) ∈ V) →
            (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), b ∈ y → ∀ hb : (b : ↥Kℓ) ∈ V, (⟨(b : ↥Kℓ), hb⟩ : ↥V) ∈ maximalIdeal ↥V) →
            (∀ f : ↥Kℓ, f ∈ Bt → f ∈ V) ∨
            (∃ O ∈ ends, ∀ (f : ↥Kℓ) (hfO : f ∈ O), f ∈ V ∧ (¬ IsUnit (⟨f, hfO⟩ : ↥O) → ∀ hfV : f ∈ V, (⟨f, hfV⟩ : ↥V) ∈ maximalIdeal ↥V))))
    (hR9 : (∃ b : ↥Kℓ, b ∈ Bt ∧ ∀ V : ValuationSubring ↥Kℓ, (∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ V ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x) →
            (∀ hϖV : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ ∈ V, (⟨algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩, hϖV⟩ : ↥V) ∈ maximalIdeal ↥V) →
            (∀ hjV : (jℓ : ↥Kℓ) ∈ V, (∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), p.Monic →
                ∀ hp : Polynomial.aeval (jℓ : ↥Kℓ) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)) ∈ V,
                  (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) → b ∉ V)))
    (hR10 : (∀ y'' : Ideal ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), y''.IsMaximal → algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ⟨π₀, hπ⟩ ∈ y'' →
            (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
              ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
                ¬ (∀ (b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) (hb : τ (b : ↥Kℓ) ∈ chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ),
                    b ∈ y ↔ (⟨τ (b : ↥Kℓ), hb⟩ : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) ∈ y'')) →
            ∃ b : ↥Kℓ, b ∈ Bt ∧ ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
              ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
              ∀ V : ValuationSubring ↥Kℓ,
                (∀ c : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (c : ↥Kℓ) ∈ V) →
                (∀ (c : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) (hc : τ.symm (c : ↥Kℓ) ∈ chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ),
                    (⟨τ.symm (c : ↥Kℓ), hc⟩ : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) ∈ y'' → ∀ hcV : (c : ↥Kℓ) ∈ V, (⟨(c : ↥Kℓ), hcV⟩ : ↥V) ∈ maximalIdeal ↥V) →
                b ∉ V))
    (hn : n = 2 * placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (G : Subgroup (↥Kℓ ≃ₐ[↥k₀] ↥Kℓ))
    (hG : G = Subgroup.closure {τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ | ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
      ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ})
    (K₀ : IntermediateField ↥k₀ ↥Kℓ)
    (hK₀ : K₀ = IntermediateField.fixedField G)
    (B₀ : Subalgebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)
    (hB₀ : ∀ f : ↥Kℓ, f ∈ B₀ ↔ f ∈ Bt ∧ ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, τ ∈ G → τ f = f)
    (W₀' : ValuationSubring ↥K₀)
    (hW₀' : ∀ f : ↥K₀, f ∈ W₀' ↔ ((f : ↥Kℓ)) ∈ Wt)

    (nodes : Finset (Subring ↥K₀)) (Õ : Subring ↥Kℓ) (O : Subring ↥K₀)

    (hÕ : Õ ∈ ends)
    (hO : ∀ f : ↥K₀, f ∈ O ↔ (f : ↥Kℓ) ∈ Õ)
    (hGfin : Finite ↥G)
    (hτ₀G : τ₀ ∈ G)
    (hGatt : ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, τ ∈ G → ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
          ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ)
    (hτ₀n : ∀ f : ↥Kℓ, (τ₀ ^ n) f = f)
    (hHcyc : ∀ σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, σ ∈ G → (∀ f : ↥Kℓ, f ∈ Õ ↔ σ f ∈ Õ) → ∃ j : ℕ, ∀ f : ↥Kℓ, σ f = (τ₀ ^ j) f)
    (hInvFin : ∀ (Bx : Subalgebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ) (BG : Subring ↥Kℓ), Algebra.FiniteType ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bx →
          (∀ σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, σ ∈ G → ∀ f : ↥Kℓ, f ∈ Bx → σ f ∈ Bx) →
          (∀ f : ↥Kℓ, f ∈ BG ↔ f ∈ Bx ∧ ∀ σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, σ ∈ G → σ f = f) →
          IsNoetherianRing ↥BG ∧ (∀ (hle : BG ≤ Bx.toSubring), letI := (Subring.inclusion hle).toAlgebra; Module.Finite ↥BG ↥Bx.toSubring) ∧
          (∃ T : Finset ↥K₀, Bx.toSubring.comap (algebraMap ↥K₀ ↥Kℓ) = Subring.closure
            ({f : ↥K₀ | ∃ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ∧ f = algebraMap ↥k₀ ↥K₀ x} ∪ (↑T : Set ↥K₀))))
    (hAdom : IsDomain (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hAdvr : IsDiscreteValuationRing (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hAcompl : IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hπhat : maximalIdeal (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) = Ideal.span {(algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩)})
    (hnunit : IsUnit ((n : ℕ) : (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))))
    (hmodelloc : IsLocalRing (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m)))
    (hmodelcompl : IsAdicComplete (maximalIdeal (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))) (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m)))
    (hsplit₁ : ∀ Wx : ValuationSubring ↥Kℓ, (∀ f : ↥Kℓ, f ∈ Õ → f ∈ Wx) → IsDiscreteValuationRing ↥Wx →
          (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (b : ↥Kℓ) ∈ Wx) →
          (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (∀ hb : (b : ↥Kℓ) ∈ Wx, (⟨(b : ↥Kℓ), hb⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) → b ∈ y) →
          (∃ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), b ∈ y ∧ ∀ hb : (b : ↥Kℓ) ∈ Wx, (⟨(b : ↥Kℓ), hb⟩ : ↥Wx) ∉ maximalIdeal ↥Wx) →
          ∃ f : ↥Kℓ, f ∈ chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ ∧ (∀ σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, σ ∈ G → σ f = f) ∧
            (∀ hfW : f ∈ Wt, (⟨f, hfW⟩ : ↥Wt) ∈ maximalIdeal ↥Wt) ∧ (∀ hfX : f ∈ Wx, (⟨f, hfX⟩ : ↥Wx) ∉ maximalIdeal ↥Wx))
    (hsplit₂ : ∀ (c : ↥Kℓ) (hcO : c ∈ Õ), ¬ IsUnit (⟨c, hcO⟩ : ↥Õ) → (∀ hcW : c ∈ Wt, (⟨c, hcW⟩ : ↥Wt) ∉ maximalIdeal ↥Wt) →
          ∃ (f : ↥Kℓ) (hfO : f ∈ Õ), (∀ σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, σ ∈ G → σ f = f) ∧ ¬ IsUnit (⟨f, hfO⟩ : ↥Õ) ∧
            (∀ hfW : f ∈ Wt, (⟨f, hfW⟩ : ↥Wt) ∉ maximalIdeal ↥Wt))
    (hN3wit : ∀ Wx : ValuationSubring ↥Kℓ, (∀ f : ↥Kℓ, f ∈ Õ → f ∈ Wx) → IsDiscreteValuationRing ↥Wx →
          (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (b : ↥Kℓ) ∈ Wx) →
          (∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ Wx ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x) →
          (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (∀ hb : (b : ↥Kℓ) ∈ Wx, (⟨(b : ↥Kℓ), hb⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) → b ∈ y) →
          (∃ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), b ∈ y ∧ ∀ hb : (b : ↥Kℓ) ∈ Wx, (⟨(b : ↥Kℓ), hb⟩ : ↥Wx) ∉ maximalIdeal ↥Wx) →
          (∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))),
            (∃ hm : Polynomial.aeval (⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)) ∈ Wx, (⟨_, hm⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
            ∀ i, p.coeff i ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) →
          ∃ t : ↥(Wx.comap (algebraMap ↥K₀ ↥Kℓ)), ∀ p : Polynomial ↥k₀, (∀ i, ((p.coeff i : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A) →
            (∃ hm : Polynomial.aeval (t : ↥K₀) p ∈ Wx.comap (algebraMap ↥K₀ ↥Kℓ), (⟨_, hm⟩ : ↥(Wx.comap (algebraMap ↥K₀ ↥Kℓ))) ∈ maximalIdeal ↥(Wx.comap (algebraMap ↥K₀ ↥Kℓ))) →
              ∀ i, ∃ hc : algebraMap ↥k₀ ↥K₀ (p.coeff i) ∈ Wx.comap (algebraMap ↥K₀ ↥Kℓ), (⟨_, hc⟩ : ↥(Wx.comap (algebraMap ↥K₀ ↥Kℓ))) ∈ maximalIdeal ↥(Wx.comap (algebraMap ↥K₀ ↥Kℓ)))
    (hN3laws : ∀ Wx : ValuationSubring ↥Kℓ, (∀ f : ↥Kℓ, f ∈ Õ → f ∈ Wx) →
          (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (b : ↥Kℓ) ∈ Wx) →
          (∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ Wx ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x) →
          (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (∀ hb : (b : ↥Kℓ) ∈ Wx, (⟨(b : ↥Kℓ), hb⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) → b ∈ y) →
          (∃ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), b ∈ y ∧ ∀ hb : (b : ↥Kℓ) ∈ Wx, (⟨(b : ↥Kℓ), hb⟩ : ↥Wx) ∉ maximalIdeal ↥Wx) →
          (∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))),
            (∃ hm : Polynomial.aeval (⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)) ∈ Wx, (⟨_, hm⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
            ∀ i, p.coeff i ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) →
          ∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
            (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
            (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
              0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
              0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
                ↥(modularFunctionFieldBar M'))) →
            ∀ (hgK : (coeffEmb ↥k₀ g) ∈ Kℓ), ∃ hF : (⟨(coeffEmb ↥k₀ g), hgK⟩ : ↥Kℓ) ∈ K₀,
              (⟨_, hF⟩ : ↥K₀) ∈ Wx.comap (algebraMap ↥K₀ ↥Kℓ) ∧
              (∀ hW : (⟨_, hF⟩ : ↥K₀) ∈ Wx.comap (algebraMap ↥K₀ ↥Kℓ), (⟨_, hW⟩ : ↥(Wx.comap (algebraMap ↥K₀ ↥Kℓ))) ∈ maximalIdeal ↥(Wx.comap (algebraMap ↥K₀ ↥Kℓ)) ↔
                (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') = 0) ∧
              ((R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                  (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
                (⟨_, hF⟩ : ↥K₀) ∈ O ∧
                ∀ (hO' : (⟨_, hF⟩ : ↥K₀) ∈ O) (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A) (hcO : algebraMap ↥k₀ ↥K₀ c ∈ O),
                  residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
                    (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
                  ¬ IsUnit ((⟨_, hO'⟩ : ↥O) - ⟨_, hcO⟩)))
    (hN4frac : ∀ (Bx : Subalgebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ), (∀ σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, σ ∈ G → ∀ f : ↥Kℓ, f ∈ Bx → σ f ∈ Bx) →
          (∀ f : ↥Kℓ, f ∈ Bx → f ∈ Õ) →
          (∀ f : ↥Kℓ, f ∈ Õ ↔ ∃ g h : ↥Kℓ, g ∈ Bx ∧ h ∈ Bx ∧ (∀ hh : h ∈ Õ, IsUnit (⟨h, hh⟩ : ↥Õ)) ∧ f * h = g) →
          ∀ f : ↥K₀, ∃ g h : ↥K₀, (g : ↥Kℓ) ∈ Bx ∧ (h : ↥Kℓ) ∈ Bx ∧ h ≠ 0 ∧ f * h = g)
    (hjfix : ∀ σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, σ ∈ G → σ (⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) = (⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ))
    (hN5 : ∀ (Bx : Subalgebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ), (∀ σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, σ ∈ G → ∀ f : ↥Kℓ, f ∈ Bx → σ f ∈ Bx) →
          (∃ b : ↥Kℓ, b ∈ Bx ∧ ∀ V : ValuationSubring ↥Kℓ, (∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ V ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x) →
                    (∀ hϖV : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ ∈ V, (⟨algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩, hϖV⟩ : ↥V) ∈ maximalIdeal ↥V) →
                    (∀ hjV : (jℓ : ↥Kℓ) ∈ V, (∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), p.Monic →
                        ∀ hp : Polynomial.aeval (jℓ : ↥Kℓ) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)) ∈ V,
                          (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) →
                      (∃ f : ↥Kℓ, f ∈ Õ ∧ f ∉ V) → b ∉ V)) →
          (∃ b : ↥K₀, b ∈ Bx.toSubring.comap (algebraMap ↥K₀ ↥Kℓ) ∧ ∀ V : ValuationSubring ↥K₀,
                      (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥K₀ x ∈ V) →
                      (∀ hπV : algebraMap ↥k₀ ↥K₀ π₀ ∈ V, (⟨_, hπV⟩ : ↥V) ∈ maximalIdeal ↥V) →
                      ∀ (hjK' : (coeffEmb ↥k₀ jq) ∈ Kℓ) (hjF : (⟨(coeffEmb ↥k₀ jq), hjK'⟩ : ↥Kℓ) ∈ K₀) (hjV : (⟨_, hjF⟩ : ↥K₀) ∈ V),
                        (∀ p : Polynomial ↥k₀, p.Monic → (∀ i : ℕ, ((p.coeff i : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A) →
                          ∀ hp : Polynomial.aeval (⟨_, hjF⟩ : ↥K₀) (p.map (algebraMap ↥k₀ ↥K₀)) ∈ V,
                            (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) →
                      (∃ f : ↥K₀, f ∈ O ∧ f ∉ V) → b ∉ V))
    (hIGSEP : ∀ Wx : ValuationSubring ↥Kℓ, (∀ f : ↥Kℓ, f ∈ Õ → f ∈ Wx) → IsDiscreteValuationRing ↥Wx →
          (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (b : ↥Kℓ) ∈ Wx) →
          (∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ Wx ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x) →
          (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (∀ hb : (b : ↥Kℓ) ∈ Wx, (⟨(b : ↥Kℓ), hb⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) → b ∈ y) →
          (∃ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), b ∈ y ∧ ∀ hb : (b : ↥Kℓ) ∈ Wx, (⟨(b : ↥Kℓ), hb⟩ : ↥Wx) ∉ maximalIdeal ↥Wx) →
          (∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))),
            (∃ hm : Polynomial.aeval (⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)) ∈ Wx, (⟨_, hm⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
            ∀ i, p.coeff i ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) →
          (∀ O' ∈ ends, O' ≠ Õ → ∃ f : ↥Kℓ, f ∈ O' ∧ f ∉ Wx) →
          (∀ O' ∈ ends, ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
            ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
            (∀ f : ↥Kℓ, f ∈ O' → τ f ∈ Wx) → O' = Õ) →
          ∀ O' ∈ nodes, O' ≠ O → ∃ f : ↥K₀, f ∈ O' ∧ f ∉ Wx.comap (algebraMap ↥K₀ ↥Kℓ)) :

    (

                (∀ f : ↥K₀, f ∈ O → f ∈ W₀') ∧ ∃ (_ : IsLocalRing ↥O) (_ : IsNoetherianRing ↥O),
                (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥K₀ x ∈ O) ∧
                (∀ (f : ↥K₀) (hf : f ∈ O), ∃ (x : ↥k₀) (hx : algebraMap ↥k₀ ↥K₀ x ∈ O), (x : (AlgebraicClosure ℚ)) ∈ A ∧
                  ¬ IsUnit ((⟨f, hf⟩ : ↥O) - ⟨_, hx⟩)) ∧

                (∃ (E₀ : ℕ) (_ : 1 ≤ E₀)

                   (_ : ∃ v : ↥k₀, (v : (AlgebraicClosure ℚ)) ∈ A ∧ ((v⁻¹ : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A ∧
                      π₀ ^ E₀ = ϖt ^ (2 * placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))) * v)
                   (hπO : algebraMap ↥k₀ ↥K₀ π₀ ∈ O) (cx cy : ↥O) (u : (↥O)ˣ)
                   (ι : (AdicCompletion (maximalIdeal ↥O) ↥O) ≃+* UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀))
                   (γU γV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀))ˣ),
                  cx * cy = (⟨_, hπO⟩ : ↥O) ^ E₀ * (u : ↥O) ∧
                  (∀ (x : ↥k₀) (hx : (x : (AlgebraicClosure ℚ)) ∈ A) (hxO : algebraMap ↥k₀ ↥K₀ x ∈ O),
                    ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, hxO⟩) =
                      UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨x, hx⟩)) ∧
                  ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cx) = (γU : UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) * UVCrossingModel.U ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) ∧
                  ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cy) = (γV : UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) * UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) ∧
                  ((cy : ↥K₀) ∈ W₀') ∧ (∀ hcy : (cy : ↥K₀) ∈ W₀', (⟨(cy : ↥K₀), hcy⟩ : ↥W₀') ∈ maximalIdeal ↥W₀') ∧
                  (∀ hcx : (cx : ↥K₀) ∈ W₀', (⟨(cx : ↥K₀), hcx⟩ : ↥W₀') ∉ maximalIdeal ↥W₀') ∧

                  (∃ (hjF : (⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a₀ ∈ K₀)
                     (hjO : (⟨_, hjF⟩ : ↥K₀) ∈ O) (e : ℕ) (wV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀))ˣ), 1 ≤ e ∧
                    ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, hjO⟩) =
                      (wV : UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) * (UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) ^ e) ∧

                  (∃ Wx : ValuationSubring ↥K₀,
                    (∀ f : ↥K₀, f ∈ O → f ∈ Wx) ∧
                    (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥K₀ x ∈ Wx) ∧
                    IsDiscreteValuationRing ↥Wx ∧
                    (∃ hπW : algebraMap ↥k₀ ↥K₀ π₀ ∈ Wx, maximalIdeal ↥Wx = Ideal.span {(⟨_, hπW⟩ : ↥Wx)}) ∧
                    (∃ t : ↥Wx, ∀ p : Polynomial ↥k₀, (∀ n, ((p.coeff n : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A) →
                      (∃ hm : Polynomial.aeval (t : ↥K₀) p ∈ Wx, (⟨_, hm⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
                        ∀ n, ∃ hc : algebraMap ↥k₀ ↥K₀ (p.coeff n) ∈ Wx, (⟨_, hc⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) ∧
                    (∀ hcx : (cx : ↥K₀) ∈ Wx, (⟨(cx : ↥K₀), hcx⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) ∧
                    (∀ hcy : (cy : ↥K₀) ∈ Wx, (⟨(cy : ↥K₀), hcy⟩ : ↥Wx) ∉ maximalIdeal ↥Wx) ∧
                    (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
                      (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
                      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
                        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
                        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
                          ↥(modularFunctionFieldBar M'))) →
                      ∀ (hgK : (coeffEmb ↥k₀ g) ∈ Kℓ), ∃ hF : (⟨(coeffEmb ↥k₀ g), hgK⟩ : ↥Kℓ) ∈ K₀,
                        (⟨_, hF⟩ : ↥K₀) ∈ Wx ∧
                        (∀ hW : (⟨_, hF⟩ : ↥K₀) ∈ Wx, (⟨_, hW⟩ : ↥Wx) ∈ maximalIdeal ↥Wx ↔
                          (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') = 0) ∧
                        ((R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
                          (⟨_, hF⟩ : ↥K₀) ∈ O ∧
                          ∀ (hO : (⟨_, hF⟩ : ↥K₀) ∈ O) (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A) (hcO : algebraMap ↥k₀ ↥K₀ c ∈ O),
                            residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
                              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
                            ¬ IsUnit ((⟨_, hO⟩ : ↥O) - ⟨_, hcO⟩))) ∧

                    (∀ O' ∈ nodes, O' ≠ O → ∃ f : ↥K₀, f ∈ O' ∧ f ∉ Wx)) ∧

                  (∃ Bx : Subring ↥K₀,
                    (∀ f : ↥K₀, f ∈ Bx → (f : ↥Kℓ) ∈ B₀ ∧ f ∈ O) ∧
                    (∀ (f : ↥K₀), f ∈ Bx → ∀ P : Place ↥k₀ ↥Kℓ,
                      0 ≤ P.ord (jℓ : ↥Kℓ) → 0 ≤ P.ord (f : ↥Kℓ)) ∧
                    (∀ f : ↥K₀, f ∈ O ↔ ∃ g h : ↥K₀, g ∈ Bx ∧ h ∈ Bx ∧ (∀ hh : h ∈ O, IsUnit (⟨h, hh⟩ : ↥O)) ∧ f * h = g) ∧
                    (∀ f : ↥K₀, ∃ g h : ↥K₀, g ∈ Bx ∧ h ∈ Bx ∧ h ≠ 0 ∧ f * h = g) ∧
                    (∃ T : Finset ↥K₀, Bx = Subring.closure
                      ({f : ↥K₀ | ∃ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ∧ f = algebraMap ↥k₀ ↥K₀ x} ∪ (↑T : Set ↥K₀))) ∧

                    (∃ b : ↥K₀, b ∈ Bx ∧ ∀ V : ValuationSubring ↥K₀,
                      (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥K₀ x ∈ V) →
                      (∀ hπV : algebraMap ↥k₀ ↥K₀ π₀ ∈ V, (⟨_, hπV⟩ : ↥V) ∈ maximalIdeal ↥V) →
                      ∀ (hjK' : (coeffEmb ↥k₀ jq) ∈ Kℓ) (hjF : (⟨(coeffEmb ↥k₀ jq), hjK'⟩ : ↥Kℓ) ∈ K₀) (hjV : (⟨_, hjF⟩ : ↥K₀) ∈ V),
                        (∀ p : Polynomial ↥k₀, p.Monic → (∀ i : ℕ, ((p.coeff i : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A) →
                          ∀ hp : Polynomial.aeval (⟨_, hjF⟩ : ↥K₀) (p.map (algebraMap ↥k₀ ↥K₀)) ∈ V,
                            (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) →
                      (∃ f : ↥K₀, f ∈ O ∧ f ∉ V) → b ∉ V))) ) := by
  classical

  have h76 := hR7.2.2.2.2.2.2.1
  have h78 := hR7.2.2.2.2.2.2.2.2.2.2.1
  have hend := h78 Õ hÕ
  obtain ⟨hÕWt, hend⟩ := hend
  obtain ⟨hÕloc, hend⟩ := hend
  obtain ⟨hÕnoeth, hend⟩ := hend
  haveI := hÕloc
  haveI := hÕnoeth
  obtain ⟨hCÕ, hend⟩ := hend
  obtain ⟨hconstÕ, hend⟩ := hend
  obtain ⟨hresÕ, hRN2⟩ := hend
  obtain ⟨hϖÕ, hRN2⟩ := hRN2
  obtain ⟨cxu, hRN2⟩ := hRN2
  obtain ⟨cyu, hRN2⟩ := hRN2
  obtain ⟨uu, hRN2⟩ := hRN2
  obtain ⟨ιt, hRN2⟩ := hRN2
  obtain ⟨γUu, hRN2⟩ := hRN2
  obtain ⟨γVu, hRN2⟩ := hRN2
  obtain ⟨θ₀, hRN2⟩ := hRN2
  obtain ⟨ζc', hRN2⟩ := hRN2
  obtain ⟨hζζ', hRN2⟩ := hRN2
  obtain ⟨hmodloc, hRN2⟩ := hRN2
  obtain ⟨hcxyu, hRN2⟩ := hRN2
  obtain ⟨hconstu, hRN2⟩ := hRN2
  obtain ⟨hιcxu, hRN2⟩ := hRN2
  obtain ⟨hιcyu, hRN2⟩ := hRN2
  obtain ⟨hcyuWt, hRN2⟩ := hRN2
  obtain ⟨hcxuWt, hRN2⟩ := hRN2
  obtain ⟨hRN10, hRN2⟩ := hRN2
  obtain ⟨hjaÕ, hRN10⟩ := hRN10
  obtain ⟨eup, hRN10⟩ := hRN10
  obtain ⟨wVu, hRN10⟩ := hRN10
  obtain ⟨heup, hjgerm⟩ := hRN10
  obtain ⟨hequiv, hRN2⟩ := hRN2
  obtain ⟨htanU, hRN2⟩ := hRN2
  obtain ⟨htanV, hRN2⟩ := hRN2
  obtain ⟨hRN3, hRN4⟩ := hRN2
  obtain ⟨Wxu, hRN3⟩ := hRN3
  obtain ⟨hÕWx, hRN3⟩ := hRN3
  obtain ⟨hCWx, hRN3⟩ := hRN3
  obtain ⟨hconstWx, hRN3⟩ := hRN3
  obtain ⟨hWxdvr, hRN3⟩ := hRN3
  obtain ⟨hRN3unif, hRN3⟩ := hRN3
  obtain ⟨hϖWx, hWxunif⟩ := hRN3unif
  obtain ⟨-, hRN3⟩ := hRN3
  obtain ⟨hRN3j, hRN3⟩ := hRN3
  obtain ⟨hcxuWx, hRN3⟩ := hRN3
  obtain ⟨hcyuWx, hRN3⟩ := hRN3
  obtain ⟨hWxy, hRN3⟩ := hRN3
  obtain ⟨hWxy', hRN3⟩ := hRN3
  obtain ⟨hRN3sep, hRN3sepP⟩ := hRN3
  obtain ⟨Bx, hRN4⟩ := hRN4
  obtain ⟨hBxBtO, hRN4⟩ := hRN4
  obtain ⟨hBxft, hRN4⟩ := hRN4
  obtain ⟨hBxstab, hRN4⟩ := hRN4
  obtain ⟨hBxreg, hRN4⟩ := hRN4
  obtain ⟨hBxloc, hRN9⟩ := hRN4
  haveI := hmodloc
  haveI := hAdom
  haveI := hAdvr
  haveI := hAcompl
  haveI := hmodelcompl
  haveI := hGfin
  haveI := hWxdvr

  have hmemK₀ : ∀ f : ↥Kℓ, f ∈ K₀ ↔ ∀ σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, σ ∈ G → σ f = f := by
    intro f; rw [hK₀, IntermediateField.mem_fixedField_iff]
  have halgK₀ : ∀ f : ↥K₀, algebraMap ↥K₀ ↥Kℓ f = (f : ↥Kℓ) := fun _ => rfl
  have halgk₀ : ∀ x : ↥k₀, ((algebraMap ↥k₀ ↥K₀ x : ↥K₀) : ↥Kℓ) = algebraMap ↥k₀ ↥Kℓ x := fun _ => rfl
  have halgA : ∀ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a = algebraMap ↥k₀ ↥Kℓ (a : ↥k₀) := fun a =>
    IsScalarTower.algebraMap_apply ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥Kℓ a
  have hfixk₀ : ∀ (σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ) (x : ↥k₀), σ (algebraMap ↥k₀ ↥Kℓ x) = algebraMap ↥k₀ ↥Kℓ x := fun σ x => σ.commutes x

  have hBxG : ∀ σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, σ ∈ G → ∀ f : ↥Kℓ, f ∈ Bx → σ f ∈ Bx := by
    intro σ hσ f hf
    have happ1 := hGatt σ hσ
    obtain ⟨γ, hγ1, hγ2, hatt⟩ := happ1
    exact hBxstab γ hγ1 hγ2 σ hatt f hf
  have hBxÕ : Bx.toSubring ≤ Õ := fun f hf => (hBxBtO f hf).2

  let O₀ : Subring ↥Kℓ := Õ ⊓ K₀.toSubring
  have hO₀ : ∀ f : ↥Kℓ, f ∈ O₀ ↔ f ∈ Õ ∧ ∀ σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, σ ∈ G → σ f = f := by
    intro f; rw [Subring.mem_inf]; exact and_congr Iff.rfl ((Iff.rfl : f ∈ K₀.toSubring ↔ f ∈ K₀).trans (hmemK₀ f))
  let BxG : Subring ↥Kℓ := Bx.toSubring ⊓ K₀.toSubring
  have hBxGdef : ∀ f : ↥Kℓ, f ∈ BxG ↔ f ∈ Bx ∧ ∀ σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, σ ∈ G → σ f = f := by
    intro f; rw [Subring.mem_inf]; exact and_congr Iff.rfl ((Iff.rfl : f ∈ K₀.toSubring ↔ f ∈ K₀).trans (hmemK₀ f))
  have happ2 := hInvFin Bx BxG hBxft hBxG hBxGdef
  obtain ⟨hBxGnoeth, hBxGfin, ⟨T, hT⟩⟩ := happ2
  have hcO₀ : ∀ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a ∈ O₀ := by
    intro a
    rw [hO₀, halgA]
    exact ⟨(hconstÕ (a : ↥k₀)).mpr ⟨a, rfl⟩, fun σ _ => hfixk₀ σ _⟩
  have hζcprim' : ∀ j : ℕ, 0 < j → j < n → ζc ^ j ≠ 1 := by
    intro j hj hjn h
    have := hζcprim j hj hjn
    rw [h, sub_self] at this
    exact not_isUnit_zero this

  have happ3 :=
    pernode_core G hGfin Bx.toSubring hBxG BxG hBxGdef hBxGnoeth hBxGfin Õ hBxÕ hBxloc O₀ hO₀
      τ₀ hτ₀G (h76 Õ hÕ) n hn1 hτ₀n hHcyc (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) hπhat m hm1 hnunit ζc ζc' hζζ' hζc hζcprim' ιt θ₀ htanU htanV hequiv
      (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ) (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))) hcO₀ hconstu
  obtain ⟨-, hO₀loc, hO₀noeth, hle, κ, ι₀, ψ, γ, hunits, hκof, hκinj, hrangeθ, hψinj, hψconst, hγ1, hψU, hψV, hψrange, hsquare, hι₀const, hordθ⟩ := happ3
  haveI := hO₀loc
  haveI := hO₀noeth

  have hOO₀ : ∀ f : ↥K₀, f ∈ O ↔ algebraMap ↥K₀ ↥Kℓ f ∈ O₀ := by
    intro f
    rw [hO, hO₀, halgK₀]
    exact ⟨fun h => ⟨h, (hmemK₀ _).mp f.2⟩, fun h => h.1⟩
  have hO₀surj : ∀ g : ↥Kℓ, g ∈ O₀ → ∃ f : ↥K₀, algebraMap ↥K₀ ↥Kℓ f = g := by
    intro g hg
    exact ⟨⟨g, (hmemK₀ g).mpr ((hO₀ g).mp hg).2⟩, rfl⟩
  let e : ↥O ≃+* ↥O₀ := subringEquivOfMemIff (algebraMap ↥K₀ ↥Kℓ) O O₀ hOO₀ hO₀surj
  have he : ∀ f : ↥O, (e f : ↥Kℓ) = ((f : ↥K₀) : ↥Kℓ) := fun f => subringEquivOfMemIff_apply _ _ _ _ _ f
  haveI hOloc : IsLocalRing ↥O := IsLocalRing.of_surjective' e.symm.toRingHom e.symm.surjective
  haveI hOnoeth : IsNoetherianRing ↥O := isNoetherianRing_of_ringEquiv ↥O₀ e.symm
  have eunit : ∀ x : ↥O, IsUnit x ↔ IsUnit (e x) := fun x =>
    ⟨fun h => h.map e.toRingHom, fun h => by have := h.map e.symm.toRingHom; simpa using this⟩
  have hunitsO : ∀ f : ↥O, IsUnit f ↔ IsUnit (⟨((f : ↥K₀) : ↥Kℓ), (hO f).mp f.2⟩ : ↥Õ) := by
    intro f
    rw [eunit, hunits]
    exact Iff.of_eq (congrArg IsUnit (Subtype.ext (he f)))

  let b : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) →+* ↥O₀ :=
    { toFun := fun a => ⟨algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a, hcO₀ a⟩
      map_one' := Subtype.ext (by change algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ 1 = 1; exact map_one _)
      map_mul' := fun x z => Subtype.ext (by change algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ (x * z) = algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ x * algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ z; exact map_mul _ _ _)
      map_zero' := Subtype.ext (by change algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ 0 = 0; exact map_zero _)
      map_add' := fun x z => Subtype.ext (by change algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ (x + z) = algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ x + algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ z; exact map_add _ _ _) }
  have hb : ∀ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), b a = ⟨algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a, hcO₀ a⟩ := fun _ => rfl
  have happ4 :=
    IsLocalRing.exists_ringHom_ringEquiv_adicCompletion_uvCrossingModel_of_ringEquiv (A₀ := ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩ (m * n)
      (R := ↥O₀) b ι₀ (fun a => by rw [hb]; exact hι₀const a) (N := ↥O) e.symm
  obtain ⟨σc, ιO, hσc, hιOconst, hιOe⟩ := happ4

  have hιOconst' : ∀ (x : ↥k₀) (hx : (x : (AlgebraicClosure ℚ)) ∈ A) (hxO : algebraMap ↥k₀ ↥K₀ x ∈ O),
      ιO (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, hxO⟩) =
        UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ (m * n)) (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨x, hx⟩) := by
    intro x hx hxO
    have h1 : (⟨_, hxO⟩ : ↥O) = e.symm (b ⟨x, hx⟩) := by
      apply e.injective
      rw [RingEquiv.apply_symm_apply]
      apply Subtype.ext
      rw [he, hb]
      change ((algebraMap ↥k₀ ↥K₀ x : ↥K₀) : ↥Kℓ) = algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨x, hx⟩
      rw [halgk₀, halgA]
    exact (congrArg (fun r => ιO (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) r)) h1).trans
      ((hιOe (b ⟨x, hx⟩)).trans (hι₀const ⟨x, hx⟩))

  have hπO : algebraMap ↥k₀ ↥K₀ π₀ ∈ O := by
    rw [hO, halgk₀, ← halgA ⟨π₀, hπ⟩]; exact hϖÕ
  have ht : ιO (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, hπO⟩) =
      UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ (m * n)) (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) := hιOconst' π₀ hπ hπO

  let Wx : ValuationSubring ↥K₀ := Wxu.comap (algebraMap ↥K₀ ↥Kℓ)
  have hWx : ∀ f : ↥K₀, f ∈ Wx ↔ (f : ↥Kℓ) ∈ Wxu := fun f => ValuationSubring.mem_comap
  have hOWx : ∀ f : ↥K₀, f ∈ O → f ∈ Wx := fun f hf => (hWx f).mpr (hÕWx _ ((hO f).mp hf))
  have hOW₀ : ∀ f : ↥K₀, f ∈ O → f ∈ W₀' := fun f hf => (hW₀' f).mpr (hÕWt _ ((hO f).mp hf))
  let φt : ↥O →+* ↥W₀' :=
    { toFun := fun f => ⟨(f : ↥K₀), hOW₀ _ f.2⟩
      map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl }
  let φx : ↥O →+* ↥Wx :=
    { toFun := fun f => ⟨(f : ↥K₀), hOWx _ f.2⟩
      map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl }
  let 𝔭t : Ideal ↥O := (maximalIdeal ↥W₀').comap φt
  let 𝔭x : Ideal ↥O := (maximalIdeal ↥Wx).comap φx
  haveI : 𝔭t.IsPrime := Ideal.comap_isPrime _ _
  haveI : 𝔭x.IsPrime := Ideal.comap_isPrime _ _
  have mem𝔭t : ∀ f : ↥O, f ∈ 𝔭t ↔ (⟨(f : ↥K₀), hOW₀ _ f.2⟩ : ↥W₀') ∈ maximalIdeal ↥W₀' := fun _ => Iff.rfl
  have mem𝔭x : ∀ f : ↥O, f ∈ 𝔭x ↔ (⟨(f : ↥K₀), hOWx _ f.2⟩ : ↥Wx) ∈ maximalIdeal ↥Wx := fun _ => Iff.rfl

  have maxt : ∀ (f : ↥K₀) (hf : f ∈ W₀'), (⟨f, hf⟩ : ↥W₀') ∈ maximalIdeal ↥W₀' ↔ (⟨(f : ↥Kℓ), (hW₀' f).mp hf⟩ : ↥Wt) ∈ maximalIdeal ↥Wt :=
    fun f hf => vs_mem_maximalIdeal_iff_of_mem_iff (algebraMap ↥K₀ ↥Kℓ) W₀' Wt hW₀' f hf
  have maxx : ∀ (f : ↥K₀) (hf : f ∈ Wx), (⟨f, hf⟩ : ↥Wx) ∈ maximalIdeal ↥Wx ↔ (⟨(f : ↥Kℓ), (hWx f).mp hf⟩ : ↥Wxu) ∈ maximalIdeal ↥Wxu :=
    fun f hf => vs_mem_maximalIdeal_iff_of_mem_iff (algebraMap ↥K₀ ↥Kℓ) Wx Wxu hWx f hf

  have happ5 := hsplit₁ Wxu hÕWx hWxdvr hCWx hWxy hWxy'
  obtain ⟨f₁, hf₁C, hf₁G, hf₁t, hf₁x⟩ := happ5
  have hf₁Õ : f₁ ∈ Õ := hCÕ ⟨f₁, hf₁C⟩
  have hcxu_nu : ¬ IsUnit (⟨(cxu : ↥Kℓ), cxu.2⟩ : ↥Õ) := by
    intro hu
    apply (IsLocalRing.mem_maximalIdeal _).mp (hcxuWx (hÕWx _ cxu.2))
    have h1 := (isUnit_subring_mk_iff Õ _ cxu.2).mp hu
    exact (vs_isUnit_mk_iff Wxu _ _).mpr ⟨h1.1, hÕWx _ h1.2⟩
  have happ6 := hsplit₂ (cxu : ↥Kℓ) cxu.2 hcxu_nu hcxuWt
  obtain ⟨f₂, hf₂Õ, hf₂G, hf₂nu, hf₂t⟩ := happ6
  have hf₁K : f₁ ∈ K₀ := (hmemK₀ f₁).mpr hf₁G
  have hf₂K : f₂ ∈ K₀ := (hmemK₀ f₂).mpr hf₂G
  have hf₁O : (⟨f₁, hf₁K⟩ : ↥K₀) ∈ O := (hO _).mpr hf₁Õ
  have hf₂O : (⟨f₂, hf₂K⟩ : ↥K₀) ∈ O := (hO _).mpr hf₂Õ
  have hf₁t' : (⟨_, hf₁O⟩ : ↥O) ∈ 𝔭t := by rw [mem𝔭t, maxt]; exact hf₁t _
  have hf₁x' : (⟨_, hf₁O⟩ : ↥O) ∉ 𝔭x := by rw [mem𝔭x, maxx]; exact hf₁x _
  have hf₂m : (⟨_, hf₂O⟩ : ↥O) ∈ maximalIdeal ↥O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunitsO]; exact hf₂nu
  have hf₂t' : (⟨_, hf₂O⟩ : ↥O) ∉ 𝔭t := by rw [mem𝔭t, maxt]; exact hf₂t _
  have h𝔭le : ∀ (P : Ideal ↥O) [P.IsPrime], P ≤ maximalIdeal ↥O := fun P _ => IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)
  have hne : 𝔭x ≠ 𝔭t := fun h => hf₁x' (h ▸ hf₁t')
  have hxm : 𝔭x ≠ maximalIdeal ↥O := fun h => hf₁x' (h ▸ h𝔭le 𝔭t hf₁t')
  have htm : 𝔭t ≠ maximalIdeal ↥O := fun h => hf₂t' (h.symm ▸ hf₂m)

  have hπWx : algebraMap ↥k₀ ↥K₀ π₀ ∈ Wx := hOWx _ hπO
  have hπunifx : maximalIdeal ↥Wxu = Ideal.span {(⟨algebraMap ↥K₀ ↥Kℓ (algebraMap ↥k₀ ↥K₀ π₀), (hWx _).mp hπWx⟩ : ↥Wxu)} := by
    have e0 : (⟨algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩, hϖWx⟩ : ↥Wxu) = ⟨algebraMap ↥K₀ ↥Kℓ (algebraMap ↥k₀ ↥K₀ π₀), (hWx _).mp hπWx⟩ :=
      Subtype.ext (show algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ = algebraMap ↥K₀ ↥Kℓ (algebraMap ↥k₀ ↥K₀ π₀) by rw [halgA]; rfl)
    rw [hWxunif, e0]
  have htx : (⟨_, hπO⟩ : ↥O) ∈ 𝔭x := by
    rw [mem𝔭x, maxx, hπunifx]; exact Ideal.mem_span_singleton_self _
  have hπWt : (⟨algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩, hÕWt _ hϖÕ⟩ : ↥Wt) ∈ maximalIdeal ↥Wt := by

    have hcxW : ((cxu : ↥Õ) : ↥Kℓ) ∈ Wt := hÕWt _ cxu.2
    have hcyW : ((cyu : ↥Õ) : ↥Kℓ) ∈ Wt := hÕWt _ cyu.2
    have hprod : (⟨algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩, hÕWt _ hϖÕ⟩ : ↥Wt) ^ m * ⟨((uu : ↥Õ) : ↥Kℓ), hÕWt _ (uu : ↥Õ).2⟩ =
        ⟨_, hcxW⟩ * ⟨_, hcyW⟩ := by
      apply Subtype.ext
      have := congrArg (fun z : ↥Õ => (z : ↥Kℓ)) hcxyu
      simpa using this.symm
    have hmem : (⟨algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩, hÕWt _ hϖÕ⟩ : ↥Wt) ^ m * ⟨((uu : ↥Õ) : ↥Kℓ), hÕWt _ (uu : ↥Õ).2⟩ ∈ maximalIdeal ↥Wt := by
      rw [hprod]; exact Ideal.mul_mem_left _ _ (hcyuWt hcyW)
    have huunit : IsUnit (⟨((uu : ↥Õ) : ↥Kℓ), hÕWt _ (uu : ↥Õ).2⟩ : ↥Wt) := by
      have : IsUnit ((uu : ↥Õ)) := Units.isUnit uu
      rw [isUnit_subring_mk_iff Õ _ (uu : ↥Õ).2] at this
      · exact (isUnit_subring_mk_iff Wt.toSubring _ _).mpr ⟨this.1, hÕWt _ this.2⟩
    have h2 := (Ideal.IsPrime.mem_or_mem inferInstance hmem).elim id
      (fun h => absurd h ((IsLocalRing.mem_maximalIdeal _).not.mpr (not_not.mpr huunit)))
    exact Ideal.IsPrime.mem_of_pow_mem inferInstance m h2
  have htt : (⟨_, hπO⟩ : ↥O) ∈ 𝔭t := by
    rw [mem𝔭t, maxt]
    have e1 : (⟨((algebraMap ↥k₀ ↥K₀ π₀ : ↥K₀) : ↥Kℓ), (hW₀' _).mp (hOW₀ _ hπO)⟩ : ↥Wt) = ⟨algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩, hÕWt _ hϖÕ⟩ :=
      Subtype.ext (show ((algebraMap ↥k₀ ↥K₀ π₀ : ↥K₀) : ↥Kℓ) = algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ by rw [halgA]; rfl)
    rw [e1]; exact hπWt

  have happ7 :=
    pernode_coords (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) hπhat (m * n) (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))) ιO ⟨_, hπO⟩ ht
      𝔭x 𝔭t hne htx htt hxm htm
  obtain ⟨ι', cx, cy, u, γU, γV, hι'c, hι'rel, hι'cx, hι'cy, hcxy, -, hcx_x, hcx_t, hcy_t, hcy_x, hι'x𝔭, hι't𝔭⟩ := happ7

  refine ⟨hOW₀, hOloc, hOnoeth, ?N1c, ?N1r, ?N2⟩
  case N1c =>
    intro x
    rw [hO, halgk₀, hconstÕ]
    constructor
    · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨a, rfl⟩; exact a.2
  case N1r =>
    intro f hf
    have happ8 := hresÕ (f : ↥Kℓ) ((hO f).mp hf)
    obtain ⟨a, ha, hna⟩ := happ8
    have haO : algebraMap ↥k₀ ↥K₀ (a : ↥k₀) ∈ O := by rw [hO, halgk₀, ← halgA]; exact ha
    refine ⟨(a : ↥k₀), haO, a.2, ?_⟩
    rw [hunitsO]
    convert hna using 2
    apply Subtype.ext
    change ((f - algebraMap ↥k₀ ↥K₀ (a : ↥k₀) : ↥K₀) : ↥Kℓ) = (f : ↥Kℓ) - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a
    rw [halgA]; rfl
  case N2 =>
    obtain ⟨w, hwu, hw⟩ := hm

    have hπk₀ : (π₀ : ↥k₀) ≠ 0 := by
      intro h0
      haveI := hdvr
      apply IsDiscreteValuationRing.not_a_field' (R := ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
      rw [hunif, Ideal.span_singleton_eq_bot]
      exact Subtype.ext h0
    have hπK₀ne : algebraMap ↥k₀ ↥K₀ π₀ ≠ 0 := (map_ne_zero_iff _ (algebraMap ↥k₀ ↥K₀).injective).mpr hπk₀
    have hπWxu : algebraMap ↥K₀ ↥Kℓ (algebraMap ↥k₀ ↥K₀ π₀) ∈ Wxu := (hWx _).mp hπWx
    have hπWxu_nu : ¬ IsUnit (⟨algebraMap ↥K₀ ↥Kℓ (algebraMap ↥k₀ ↥K₀ π₀), hπWxu⟩ : ↥Wxu) := by
      have : (⟨algebraMap ↥K₀ ↥Kℓ (algebraMap ↥k₀ ↥K₀ π₀), hπWxu⟩ : ↥Wxu) ∈ maximalIdeal ↥Wxu := by
        rw [hπunifx]; exact Ideal.mem_span_singleton_self _
      exact (IsLocalRing.mem_maximalIdeal _).mp this
    have hWxdvr' : IsDiscreteValuationRing ↥Wx :=
      ValuationSubring.isDiscreteValuationRing_comap_of_mem_of_not_isUnit ↥Kℓ ↥K₀ Wxu (algebraMap ↥K₀ ↥Kℓ)
        (algebraMap ↥k₀ ↥K₀ π₀) hπWxu hπWxu_nu hπK₀ne
    have happ9 := maximalIdeal_comap_eq_span_singleton Wxu (algebraMap ↥K₀ ↥Kℓ) (algebraMap ↥k₀ ↥K₀ π₀) hπWxu hπunifx
    obtain ⟨hπWx', hWxunif'⟩ := happ9

    let Bx₀ : Subring ↥K₀ := Bx.toSubring.comap (algebraMap ↥K₀ ↥Kℓ)
    have hBx₀ : ∀ f : ↥K₀, f ∈ Bx₀ ↔ (f : ↥Kℓ) ∈ Bx := fun f => Subring.mem_comap
    have happ10 := mem_iff_exists_frac_invariant G hGfin Bx.toSubring hBxG BxG hBxGdef Õ hBxÕ hBxloc O₀ hO₀
    obtain ⟨hBxGO₀, -, hfracO₀⟩ := happ10
    refine ⟨m * n, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_, hπO, cx, cy, u, ι', γU, γV,
      hcxy, fun x hx hxO => hι'c _ _ (hιOconst' x hx hxO), hι'cx, hι'cy, hOW₀ _ cy.2,
      fun hcy => (mem𝔭t cy).mp hcy_t, fun hcx h => hcx_t ((mem𝔭t cx).mpr h), ?_, ?_, ?_⟩
    ·
      have hwk : (π₀ : ↥k₀) ^ m = ϖt * (w : ↥k₀) := by
        have := congrArg (fun z : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) => (z : ↥k₀)) hw
        simpa [hϖt'] using this
      have hwinv : ((w : ↥k₀)) * ((hwu.unit⁻¹ : (↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))ˣ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) = 1 := by
        have h0 := Units.mul_inv hwu.unit
        rw [IsUnit.unit_spec] at h0
        exact congrArg Subtype.val h0
      have hw0 : (w : ↥k₀) ≠ 0 := fun h0 => by rw [h0, zero_mul] at hwinv; exact zero_ne_one hwinv
      refine ⟨(w : ↥k₀) ^ n, ?_, ?_, ?_⟩
      · exact A.toSubring.pow_mem w.2 n
      · rw [← inv_pow, ← eq_inv_of_mul_eq_one_right hwinv]
        exact A.toSubring.pow_mem ((hwu.unit⁻¹ : (↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))ˣ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))).2 n
      · rw [← hn, pow_mul, hwk, mul_pow]
    ·
      let φut : ↥Õ →+* ↥Wt :=
        { toFun := fun f => ⟨(f : ↥Kℓ), hÕWt _ f.2⟩
          map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl }
      let φux : ↥Õ →+* ↥Wxu :=
        { toFun := fun f => ⟨(f : ↥Kℓ), hÕWx _ f.2⟩
          map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl }
      let PV : Ideal ↥Õ := (maximalIdeal ↥Wt).comap φut
      let PU : Ideal ↥Õ := (maximalIdeal ↥Wxu).comap φux
      haveI : PV.IsPrime := Ideal.comap_isPrime _ _
      haveI : PU.IsPrime := Ideal.comap_isPrime _ _
      have memPV : ∀ f : ↥Õ, f ∈ PV ↔ (⟨(f : ↥Kℓ), hÕWt _ f.2⟩ : ↥Wt) ∈ maximalIdeal ↥Wt := fun _ => Iff.rfl
      have memPU : ∀ f : ↥Õ, f ∈ PU ↔ (⟨(f : ↥Kℓ), hÕWx _ f.2⟩ : ↥Wxu) ∈ maximalIdeal ↥Wxu := fun _ => Iff.rfl
      have htŨ : ιt (algebraMap ↥Õ (AdicCompletion (maximalIdeal ↥Õ) ↥Õ) ⟨_, hϖÕ⟩) = UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m) (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) :=
        hconstu ⟨π₀, hπ⟩ hϖÕ
      have htV : (⟨_, hϖÕ⟩ : ↥Õ) ∈ PV := (memPV _).mpr hπWt
      have hcyV : cyu ∈ PV := (memPV _).mpr (hcyuWt (hÕWt _ cyu.2))
      have hcxV : cxu ∉ PV := fun h => hcxuWt (hÕWt _ cxu.2) ((memPV _).mp h)
      have htU : (⟨_, hϖÕ⟩ : ↥Õ) ∈ PU := by
        rw [memPU, hWxunif]; exact Ideal.mem_span_singleton_self _
      have hcxU : cxu ∈ PU := (memPU _).mpr (hcxuWx (hÕWx _ cxu.2))
      have hcyU : cyu ∉ PU := fun h => hcyuWx (hÕWx _ cyu.2) ((memPU _).mp h)
      have happ11 := IsLocalRing.exists_branchReadings_of_ringEquiv_adicCompletion_uvCrossingModel_pow
          (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) hπhat m hm1 ιt ⟨_, hϖÕ⟩ htŨ cxu cyu γUu γVu hιcxu hιcyu PV PU htV hcyV hcxV htU hcxU hcyU
      obtain ⟨-, hD1U, -, -⟩ := happ11

      have hψfwd : ∀ z : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ (m * n))), z ∈ Ideal.span {UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ (m * n)) (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩), U ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ (m * n))} →
          ψ z ∈ Ideal.span {UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m) (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩), U ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m)} := by
        intro z hz
        have h1 : ψ z ∈ (Ideal.span {UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ (m * n)) (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩), U ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ (m * n))}).map ψ :=
          Ideal.mem_map_of_mem ψ hz
        rw [Ideal.map_span, Set.image_pair, hψconst, hψU] at h1
        refine (Ideal.span_le.mpr ?_) h1
        rintro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl
        · exact Ideal.subset_span (by simp)
        · obtain ⟨n', hn'⟩ : ∃ n' : ℕ, n = n' + 1 := ⟨n - 1, by omega⟩
          rw [hn', pow_succ, ← mul_assoc]
          exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

      have hswC' : ∀ c, crossingSwap ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ (m * n)) (UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ (m * n)) c) = UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ (m * n)) c := by
        intro c
        change crossingSwap _ (UVCrossingModel.mk _ (MvPowerSeries.C c)) = UVCrossingModel.mk _ (MvPowerSeries.C c)
        rw [crossingSwap_mk, uvSwapEquiv_C]
      have hswU' : crossingSwap ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ (m * n)) (U ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ (m * n))) = V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ (m * n)) := by
        change crossingSwap _ (UVCrossingModel.mk _ (MvPowerSeries.X 0)) = UVCrossingModel.mk _ (MvPowerSeries.X 1)
        rw [crossingSwap_mk, uvSwapEquiv_X_zero]
      have hsyC : ∀ c, (crossingSwap ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ (m * n))).symm (UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ (m * n)) c) = UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ (m * n)) c := by
        intro c
        have := congrArg (crossingSwap ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ (m * n))).symm (hswC' c)
        rw [RingEquiv.symm_apply_apply] at this
        exact this.symm
      have hsyV : (crossingSwap ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ (m * n))).symm (V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ (m * n))) = U ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ (m * n)) := by
        have := congrArg (crossingSwap ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ (m * n))).symm hswU'
        rw [RingEquiv.symm_apply_apply] at this
        exact this.symm

      have hιOe' : ∀ r : ↥O, ιO (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) r) =
          ι₀ (algebraMap ↥O₀ (AdicCompletion (maximalIdeal ↥O₀) ↥O₀) (e r)) := by
        intro r
        exact (congrArg (fun y => ιO (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) y))
          (e.symm_apply_apply r).symm).trans (hιOe (e r))
      have hincl : ∀ (r : ↥O), (Subring.inclusion hle (e r) : ↥Õ) = ⟨((r : ↥K₀) : ↥Kℓ), (hO r).mp r.2⟩ :=
        fun r => Subtype.ext (he r)

      have hι'eq : ∀ x, ι' x = ιO x := by
        rcases hι'rel with h | h
        · exact h
        · exfalso
          apply hf₁x (hÕWx _ hf₁Õ)
          have s1 := (hι't𝔭 ⟨_, hf₁O⟩).mp hf₁t'
          have s2 : ιO (algebraMap ↥O _ ⟨_, hf₁O⟩) ∈
              Ideal.span {UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ (m * n)) (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩), U ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ (m * n))} := by
            have e2 : ιO (algebraMap ↥O _ ⟨_, hf₁O⟩) = (crossingSwap _).symm (ι' (algebraMap ↥O _ ⟨_, hf₁O⟩)) :=
              ((congrArg (crossingSwap _).symm (h _)).trans ((crossingSwap _).symm_apply_apply _)).symm
            rw [e2]
            have hs := Ideal.mem_span_pair.mp s1
            obtain ⟨c, d, hcd⟩ := hs
            exact Ideal.mem_span_pair.mpr ⟨(crossingSwap _).symm c, (crossingSwap _).symm d,
              ((congrArg (crossingSwap _).symm hcd).symm.trans ((map_add _ _ _).trans
                (congrArg₂ (· + ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (hsyC _)))
                  ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl hsyV))))).symm⟩
          have s3 : ι₀ (algebraMap ↥O₀ _ (e ⟨_, hf₁O⟩)) ∈
              Ideal.span {UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ (m * n)) (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩), U ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ (m * n))} := by
            exact (hιOe' _) ▸ s2
          have s4 := hψfwd _ s3
          rw [hsquare, hκof, hincl] at s4
          exact (memPU _).mp ((hD1U ⟨f₁, hf₁Õ⟩).mpr s4)

      have hjK₀ : (⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a₀ ∈ K₀ :=
        (hmemK₀ _).mpr (fun σ hσ => by rw [map_sub, hjfix σ hσ, halgA, hfixk₀])
      have hjO : (⟨_, hjK₀⟩ : ↥K₀) ∈ O := (hO _).mpr hjaÕ
      have s6 : (Subring.inclusion hle (e ⟨_, hjO⟩) : ↥Õ) = ⟨(⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a₀, hjaÕ⟩ := by
        rw [hincl]
      have key : ψ (ι₀ (algebraMap ↥O₀ _ (e ⟨_, hjO⟩))) = (wVu : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))) * V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m) ^ eup := by
        rw [hsquare, hκof, s6]; exact hjgerm
      have happ12 := ModularCurve.UVCrossingModel.dvd_and_exists_eq_mul_pow_of_apply_eq_mul_pow_of_range_eq_fixedPoints
          (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) hπhat m hm1 n hn1 hnunit ζc ζc' hζζ' hζc hζcprim θ₀ hordθ htanU htanV ψ hψinj hψconst γ γ⁻¹ hψU hψV hψrange
      obtain ⟨hdesc, -⟩ := happ12
      have happ13 := hdesc _ eup wVu key
      obtain ⟨hdvd, w', hw'⟩ := happ13
      refine ⟨hjK₀, hjO, eup / n, w', Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) (by omega), ?_⟩
      rw [hι'eq, hιOe', hw']
    ·
      refine ⟨Wx, hOWx, ?_, hWxdvr', ⟨hπWx', hWxunif'⟩, hN3wit Wxu hÕWx hWxdvr hCWx hconstWx hWxy hWxy' hRN3j,
        fun hcx => (mem𝔭x cx).mp hcx_x, fun hcy h => hcy_x ((mem𝔭x cy).mpr h), hN3laws Wxu hÕWx hCWx hconstWx hWxy hWxy' hRN3j,
        hIGSEP Wxu hÕWx hWxdvr hCWx hconstWx hWxy hWxy' hRN3j hRN3sep hRN3sepP⟩
      intro x
      rw [hWx, halgk₀, hconstWx]
      constructor
      · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
      · rintro ⟨a, rfl⟩; exact a.2
    ·
      refine ⟨Bx₀, ?_, ?_, ?_, ?_, ⟨T, hT⟩, hN5 Bx hBxG hRN9⟩
      · intro f hf
        rw [hBx₀] at hf
        refine ⟨(hB₀ _).mpr ⟨(hBxBtO _ hf).1, (hmemK₀ _).mp f.2⟩, (hO f).mpr (hBxBtO _ hf).2⟩
      · intro f hf P hP
        rw [hBx₀] at hf
        exact hBxreg _ hf P hP
      · intro f
        constructor
        · intro hf
          have happ14 := (hfracO₀ (f : ↥Kℓ)).mp ((hOO₀ f).mp hf)
          obtain ⟨g, h, hg, hh, hhu, efh⟩ := happ14
          have hgK : g ∈ K₀ := (hmemK₀ g).mpr ((hBxGdef g).mp hg).2
          have hhK : h ∈ K₀ := (hmemK₀ h).mpr ((hBxGdef h).mp hh).2
          refine ⟨⟨g, hgK⟩, ⟨h, hhK⟩, (hBx₀ _).mpr ((hBxGdef g).mp hg).1, (hBx₀ _).mpr ((hBxGdef h).mp hh).1, fun hhO => ?_,
            Subtype.ext efh⟩
          have h1 := hhu ((hOO₀ _).mp hhO)
          rw [eunit]
          convert h1 using 2 <;> first | (with_reducible_and_instances rfl) | rfl | exact Subtype.ext (he _) | exact he _ | exact congrArg Subtype.val (he _) | (apply Subtype.ext; exact he _)
        · rintro ⟨g, h, hg, hh, hhu, efh⟩
          rw [hOO₀]
          refine (hfracO₀ (f : ↥Kℓ)).mpr ⟨(g : ↥Kℓ), (h : ↥Kℓ), (hBxGdef _).mpr ⟨(hBx₀ g).mp hg, (hmemK₀ _).mp g.2⟩,
            (hBxGdef _).mpr ⟨(hBx₀ h).mp hh, (hmemK₀ _).mp h.2⟩, fun hhO₀ => ?_, congrArg Subtype.val efh⟩
          have hhO : h ∈ O := (hOO₀ h).mpr hhO₀
          have h1 := hhu hhO
          rw [eunit] at h1
          convert h1 using 2 <;> first | (with_reducible_and_instances rfl) | rfl | exact (Subtype.ext (he _)).symm | exact (he _).symm | exact (congrArg Subtype.val (he _)).symm | (apply Subtype.ext; exact (he _).symm)
      · intro f
        have happ15 := hN4frac Bx hBxG (fun f hf => (hBxBtO f hf).2) hBxloc f
        obtain ⟨g, h, hg, hh, h0, efh⟩ := happ15
        exact ⟨g, h, (hBx₀ g).mpr hg, (hBx₀ h).mpr hh, h0, efh⟩

end S_ModularCurve_FullLevel_Diamond_pernodeConclusion_of_pernodeHyps_of_rigidChart_linkedScalars_of_eq_three_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_Diamond_pernodeConclusion_of_pernodeHyps_of_rigidChart_linkedScalars_of_eq_three_of_dvd (solution)
