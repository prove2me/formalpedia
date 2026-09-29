-- Prove2me | solution 1 for NumberField.TateGlobal.forall_ne_one_exists_continuous_monoidHom_normOneIdeleClass_apply_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/f1f9d4b0-adcc-5031-8b78-d97ab0d5b0e8

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Instances.Discrete
import Mathlib.Algebra.Module.CharacterModule
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_forall_ne_one_exists_continuous_monoidHom_normOneIdeleClass_apply_ne_one

set_option autoImplicit false

section
open Filter Topology

namespace IdeleClassSeparation

section Discrete

variable {W : Type} [AddGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W]

private theorem discreteTopology_of_isolated_zero (Γ : AddSubgroup W)
    (h : ∃ U ∈ 𝓝 (0 : W), ∀ γ ∈ Γ, γ ∈ U → γ = 0) : DiscreteTopology Γ := by
  obtain ⟨U, hU, hΓU⟩ := h
  obtain ⟨O, hOU, hO, h0O⟩ := mem_nhds_iff.mp hU
  refine discreteTopology_of_isOpen_singleton_zero ?_
  have : ({0} : Set Γ) = Subtype.val ⁻¹' O := by
    ext γ
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · rintro rfl; exact h0O
    · intro hγ; exact Subtype.ext (hΓU γ γ.2 (hOU hγ))
  rw [this]
  exact hO.preimage continuous_subtype_val

omit [IsTopologicalAddGroup W] in

private theorem exists_nhds_of_discreteTopology (Γ : AddSubgroup W) [DiscreteTopology Γ] :
    ∃ U ∈ 𝓝 (0 : W), ∀ γ ∈ Γ, γ ∈ U → γ = 0 := by
  have h0 : IsOpen ({0} : Set Γ) := isOpen_discrete _
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.mp h0
  refine ⟨O, hO.mem_nhds ?_, fun γ hγ hγO => ?_⟩
  · have : ((0 : Γ) : W) ∈ O := by
      have h : (0 : Γ) ∈ Subtype.val ⁻¹' O := by rw [hOeq]; rfl
      exact h
    simpa using this
  · have h : (⟨γ, hγ⟩ : Γ) ∈ Subtype.val ⁻¹' O := hγO
    rw [hOeq] at h
    exact congrArg Subtype.val h

end Discrete

private theorem discreteTopology_prod_of_isolated {W₁ W₂ : Type} [AddGroup W₁] [TopologicalSpace W₁]
    [IsTopologicalAddGroup W₁] [AddGroup W₂] [TopologicalSpace W₂] [IsTopologicalAddGroup W₂]
    (Γ : AddSubgroup (W₁ × W₂))
    (h₁ : ∃ U₁ ∈ 𝓝 (0 : W₁), ∀ γ ∈ Γ, γ.1 ∈ U₁ → γ.1 = 0)
    (h₂ : ∃ U₂ ∈ 𝓝 (0 : W₂), ∀ γ ∈ Γ, γ.1 = 0 → γ.2 ∈ U₂ → γ.2 = 0) : DiscreteTopology Γ := by
  obtain ⟨U₁, hU₁, hΓ₁⟩ := h₁
  obtain ⟨U₂, hU₂, hΓ₂⟩ := h₂
  refine discreteTopology_of_isolated_zero Γ ⟨U₁ ×ˢ U₂, prod_mem_nhds hU₁ hU₂, fun γ hγ hγU => ?_⟩
  have h1 : γ.1 = 0 := hΓ₁ γ hγ hγU.1
  have h2 : γ.2 = 0 := hΓ₂ γ hγ h1 hγU.2
  exact Prod.ext h1 h2

private theorem finiteIndex_of_isOpen_of_compactSpace {G : Type} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] (T : Subgroup G) (hT : IsOpen (T : Set G)) :
    T.FiniteIndex := by
  haveI : T.Normal := inferInstance
  haveI : DiscreteTopology (G ⧸ T) := QuotientGroup.discreteTopology hT
  haveI : Finite (G ⧸ T) := finite_of_compact_of_discrete
  exact Subgroup.finiteIndex_of_finite_quotient

private theorem forall_exists_pow_range {H G : Type} [CommGroup H] [CommGroup G] (f : H →* G)
    (hH : ∀ (h : H) (n : ℕ), n ≠ 0 → ∃ s : H, s ^ n = h) :
    ∀ (t : f.range) (n : ℕ), n ≠ 0 → ∃ s : f.range, s ^ n = t := by
  rintro ⟨t, ht⟩ n hn
  obtain ⟨h, rfl⟩ := MonoidHom.mem_range.mp ht
  obtain ⟨s, hs⟩ := hH h n hn
  refine ⟨⟨f s, MonoidHom.mem_range.mpr ⟨s, rfl⟩⟩, Subtype.ext ?_⟩
  simp [← hs, map_pow]

end IdeleClassSeparation
end

section
open Submodule Module

namespace IdeleClassSeparation

private theorem exists_coord_not_int_of_isZLattice {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [hdisc : DiscreteTopology L] [hlat : IsZLattice ℝ L]
    {x : E} (hx : x ∉ L) :
    ∃ ℓ : E →ₗ[ℝ] ℝ, (∀ g ∈ L, ∃ n : ℤ, ℓ g = n) ∧ ∀ n : ℤ, ℓ x ≠ n := by
  classical
  let b := Free.chooseBasis ℤ L
  let bE := b.ofZLatticeBasis ℝ L
  have hcoord : ∃ j, ∀ n : ℤ, bE.repr x j ≠ n := by
    by_contra! hcon
    choose n hn using hcon
    apply hx
    have hxe : x = ∑ j, n j • ((b j : L) : E) := by
      conv_lhs => rw [← bE.sum_repr x]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hn j, Basis.ofZLatticeBasis_apply, Int.cast_smul_eq_zsmul]
    rw [hxe]
    exact L.sum_mem fun j _ => L.smul_mem _ (b j).2
  obtain ⟨j, hj⟩ := hcoord
  refine ⟨bE.coord j, fun g hg => ⟨b.repr ⟨g, hg⟩ j, ?_⟩, hj⟩
  rw [Basis.coord_apply]
  exact Basis.ofZLatticeBasis_repr_apply ℝ L b ⟨g, hg⟩ j

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

private theorem exists_linearMap_int_on_of_discrete (Γ : Submodule ℤ V) [DiscreteTopology Γ] {y : V}
    (hy : y ∉ Γ) :
    ∃ ℓ : V →ₗ[ℝ] ℝ, (∀ g ∈ Γ, ∃ n : ℤ, ℓ g = n) ∧ ∀ n : ℤ, ℓ y ≠ n := by
  by_cases hyW : y ∈ span ℝ (Γ : Set V)
  ·
    let W : Submodule ℝ V := span ℝ (Γ : Set V)
    have hΓW : Γ ≤ W.restrictScalars ℤ := fun g hg => subset_span hg
    let L : Submodule ℤ W := comap (W.restrictScalars ℤ).subtype Γ
    let f : Γ ≃ₗ[ℤ] L := (Submodule.comapSubtypeEquivOfLe hΓW).symm
    have hdisc : DiscreteTopology L := by
      let e : Γ ≃L[ℤ] L := ⟨f, continuous_of_discreteTopology, Isometry.continuous fun _ _ => rfl⟩
      exact e.toHomeomorph.discreteTopology
    have hlat : @IsZLattice ℝ _ W _ _ L hdisc :=
      @IsZLattice.mk ℝ _ W _ _ L hdisc (by
        show span ℝ (Subtype.val ⁻¹' (Γ : Set V) : Set W) = ⊤
        exact span_span_coe_preimage)
    have hyL : (⟨y, hyW⟩ : W) ∉ L := fun h => hy h
    obtain ⟨ℓW, hℓΓ, hℓy⟩ := exists_coord_not_int_of_isZLattice L (hdisc := hdisc) (hlat := hlat) hyL
    obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective W.subtype (ker_subtype W)
    have hπW : ∀ w : W, π w = w := fun w => LinearMap.congr_fun hπ w
    refine ⟨ℓW.comp π, fun g hg => ?_, fun n => ?_⟩
    · have hπg : π g = ⟨g, hΓW hg⟩ := hπW ⟨g, hΓW hg⟩
      rw [LinearMap.comp_apply, hπg]
      exact hℓΓ ⟨g, hΓW hg⟩ hg
    · rw [LinearMap.comp_apply, hπW ⟨y, hyW⟩]
      exact hℓy n
  ·
    obtain ⟨φ, hφy, hφW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hyW inferInstance
    refine ⟨(2 * φ y)⁻¹ • φ, fun g hg => ⟨0, ?_⟩, fun n hn => ?_⟩
    · have hg0 : φ g = 0 := by
        have hmem : φ g ∈ (span ℝ (Γ : Set V)).map φ := ⟨g, subset_span hg, rfl⟩
        rwa [hφW, Submodule.mem_bot] at hmem
      simp [hg0]
    · have h2 : ((2 * φ y)⁻¹ • φ) y = (2 : ℝ)⁻¹ := by
        rw [LinearMap.smul_apply, smul_eq_mul, mul_inv, mul_assoc, inv_mul_cancel₀ hφy, mul_one]
      rw [h2] at hn
      have h1 : (2 : ℝ) * n = 1 := by rw [← hn]; norm_num
      have h3 : (2 : ℤ) * n = 1 := by exact_mod_cast h1
      omega

end IdeleClassSeparation
end

section
open Complex

namespace IdeleClassSeparation

section Extension

variable {G A : Type} [CommGroup G] [CommGroup A]

private theorem exists_monoidHom_extension (hA : ∀ (a : A) (n : ℕ), n ≠ 0 → ∃ b : A, b ^ n = a) (T : Subgroup G)
    (f : T →* A) : ∃ F : G →* A, ∀ t : T, F t = f t := by
  letI : RootableBy A ℕ := rootableByOfPowLeftSurj A ℕ fun {n} hn a => hA a n hn
  letI : RootableBy A ℤ := Group.rootableByIntOfRootableByNat A
  letI : DivisibleBy (Additive A) ℤ :=
    { div := fun a z => Additive.ofMul (RootableBy.root (Additive.toMul a) z)
      div_zero := fun a => by
        change Additive.ofMul (RootableBy.root (Additive.toMul a) (0 : ℤ)) = 0
        rw [RootableBy.root_zero]; rfl
      div_cancel := fun {z} a hz => by
        rw [← ofMul_zpow, RootableBy.root_cancel _ hz]; rfl }
  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible (Additive A)).extension_property_addMonoidHom
    (MonoidHom.toAdditive T.subtype) (fun a b hab => Subtype.ext hab) (MonoidHom.toAdditive f)
  refine ⟨AddMonoidHom.toMultiplicative h, fun t => ?_⟩
  have := DFunLike.congr_fun hh (Additive.ofMul t)
  simp at this
  exact this

end Extension

private theorem forall_exists_pow_eq_units_complex : ∀ (a : ℂˣ) (n : ℕ), n ≠ 0 → ∃ b : ℂˣ, b ^ n = a := by
  intro a n hn
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (a : ℂ) (Nat.pos_of_ne_zero hn)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at hz
    exact a.ne_zero hz.symm
  exact ⟨Units.mk0 z hz0, Units.ext (by simp [hz])⟩

private noncomputable def ratExp : ℚ →+ Additive ℂˣ where
  toFun q := Additive.ofMul (Units.mk0 (exp (2 * Real.pi * I * (q : ℂ))) (exp_ne_zero _))
  map_zero' := by
    apply Additive.toMul.injective
    apply Units.ext
    simp
  map_add' q r := by
    apply Additive.toMul.injective
    apply Units.ext
    simp only [toMul_ofMul, toMul_add, Units.val_mul, Units.val_mk0, Rat.cast_add, mul_add, Complex.exp_add]

private theorem ratExp_eq_zero_iff (q : ℚ) : ratExp q = 0 ↔ ∃ n : ℤ, (n : ℚ) = q := by
  constructor
  · intro h
    have h1 : exp (2 * Real.pi * I * (q : ℂ)) = 1 := by
      have := congrArg (fun a : Additive ℂˣ => ((Additive.toMul a : ℂˣ) : ℂ)) h
      simpa [ratExp] using this
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
    refine ⟨n, ?_⟩
    have h2 : (2 * Real.pi * I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have h3 : ((q : ℚ) : ℂ) = (n : ℂ) := by
      have := hn
      rw [mul_comm (n : ℂ)] at this
      exact mul_left_cancel₀ h2 this
    exact_mod_cast h3.symm
  · rintro ⟨n, rfl⟩
    apply Additive.toMul.injective
    apply Units.ext
    simp only [ratExp, AddMonoidHom.coe_mk, ZeroHom.coe_mk, toMul_ofMul, Units.val_mk0, toMul_zero, Units.val_one,
      Rat.cast_intCast]
    rw [show (2 * Real.pi * I * (n : ℂ)) = (n : ℂ) * (2 * Real.pi * I) by ring]
    exact Complex.exp_int_mul_two_pi_mul_I n

private noncomputable def ratCircleExp : AddCircle (1 : ℚ) →+ Additive ℂˣ :=
  QuotientAddGroup.lift _ ratExp (by
    intro q hq
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hq
    exact (ratExp_eq_zero_iff q).mpr ⟨n, by simpa using hn⟩)

private theorem ratCircleExp_eq_zero_iff (x : AddCircle (1 : ℚ)) : ratCircleExp x = 0 ↔ x = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | H q =>
    change ratExp q = 0 ↔ _
    rw [ratExp_eq_zero_iff, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff]
    constructor
    · rintro ⟨n, hn⟩; exact ⟨n, by simpa using hn⟩
    · rintro ⟨n, hn⟩; exact ⟨n, by simpa using hn⟩

private theorem exists_monoidHom_units_apply_ne_one {Q : Type} [CommGroup Q] {q : Q} (hq : q ≠ 1) :
    ∃ χ : Q →* ℂˣ, χ q ≠ 1 := by
  have hq' : (Additive.ofMul q : Additive Q) ≠ 0 := fun h => hq (by simpa using h)
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hq'
  refine ⟨AddMonoidHom.toMultiplicative (ratCircleExp.comp (c : Additive Q →+ AddCircle (1 : ℚ))), fun h => ?_⟩
  apply hc
  rw [← ratCircleExp_eq_zero_iff]
  have h' : ratCircleExp (c (Additive.ofMul q)) = 0 := by
    have := congrArg Additive.ofMul h
    simp at this
    exact this
  exact h'

section Assembly

variable {G : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

private theorem continuous_of_forall_mem_eq_one (χ : G →* ℂˣ) (S : Subgroup G) (hS : IsOpen (S : Set G))
    (h : ∀ g ∈ S, χ g = 1) : Continuous χ := by
  refine continuous_of_continuousAt_one χ ?_
  refine (continuousAt_const (y := (1 : ℂˣ))).congr ?_
  exact Filter.eventually_of_mem (hS.mem_nhds S.one_mem) fun g hg => (h g hg).symm

private theorem continuous_of_eqOn_openSubgroup (χ ψ : G →* ℂˣ) (hψ : Continuous ψ) (S : Subgroup G)
    (hS : IsOpen (S : Set G)) (h : ∀ g ∈ S, χ g = ψ g) : Continuous χ := by
  refine continuous_of_continuousAt_one χ ?_
  refine hψ.continuousAt.congr ?_
  exact Filter.eventually_of_mem (hS.mem_nhds S.one_mem) fun g hg => (h g hg).symm

private theorem exists_continuous_eq_one_on_of_notMem_sup (N S : Subgroup G) (hS : IsOpen (S : Set G)) {x : G}
    (hx : x ∉ S ⊔ N) : ∃ χ : G →* ℂˣ, Continuous χ ∧ (∀ n ∈ N, χ n = 1) ∧ χ x ≠ 1 := by
  have hx' : ((x : G ⧸ (S ⊔ N)) : G ⧸ (S ⊔ N)) ≠ 1 := by
    rwa [Ne, QuotientGroup.eq_one_iff]
  obtain ⟨φ, hφ⟩ := exists_monoidHom_units_apply_ne_one hx'
  refine ⟨φ.comp (QuotientGroup.mk' (S ⊔ N)), ?_, fun n hn => ?_, hφ⟩
  · refine continuous_of_forall_mem_eq_one _ S hS fun g hg => ?_
    simp [(QuotientGroup.eq_one_iff g).mpr (Subgroup.mem_sup_left hg)]
  · simp [(QuotientGroup.eq_one_iff n).mpr (Subgroup.mem_sup_right hn)]

private theorem exists_continuous_eq_one_on_of_eq_mul (N S : Subgroup G) (hS : IsOpen (S : Set G))
    (ψ : G →* ℂˣ) (hψ : Continuous ψ) (hψN : ∀ g ∈ S, g ∈ N → ψ g = 1) {x s n : G} (hs : s ∈ S)
    (hn : n ∈ N) (hx : x = s * n) (hψs : ψ s ≠ 1) :
    ∃ χ : G →* ℂˣ, Continuous χ ∧ (∀ m ∈ N, χ m = 1) ∧ χ x ≠ 1 := by
  let p : S × N →* G := S.subtype.coprod N.subtype
  let Ψ : S × N →* ℂˣ := (ψ.comp S.subtype).comp (MonoidHom.fst S N)
  have hker : p.ker ≤ Ψ.ker := by
    rintro ⟨a, b⟩ hab
    have hab' : (a : G) * b = 1 := hab
    have haN : (a : G) ∈ N := by
      rw [eq_inv_of_mul_eq_one_left hab']
      exact N.inv_mem b.2
    show ψ (a : G) = 1
    exact hψN a a.2 haN
  let θ : p.range →* ℂˣ :=
    (QuotientGroup.lift p.ker Ψ hker).comp (QuotientGroup.quotientKerEquivRange p).symm.toMonoidHom
  have hθ : ∀ q : S × N, θ (p.rangeRestrict q) = Ψ q := by
    intro q
    have h1 : (QuotientGroup.quotientKerEquivRange p) (QuotientGroup.mk q) = p.rangeRestrict q := rfl
    simp only [θ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← h1, MulEquiv.symm_apply_apply,
      QuotientGroup.lift_mk]
  obtain ⟨χ, hχ⟩ := exists_monoidHom_extension forall_exists_pow_eq_units_complex p.range θ
  have hχS : ∀ g ∈ S, χ g = ψ g := by
    intro g hg
    have h := hχ (p.rangeRestrict (⟨g, hg⟩, 1))
    rw [hθ] at h
    simpa [p, Ψ] using h
  have hχN : ∀ m ∈ N, χ m = 1 := by
    intro m hm
    have h := hχ (p.rangeRestrict (1, ⟨m, hm⟩))
    rw [hθ] at h
    simpa [p, Ψ] using h
  refine ⟨χ, continuous_of_eqOn_openSubgroup χ ψ hψ S hS hχS, hχN, ?_⟩
  rw [hx, map_mul, hχS s hs, hχN n hn, mul_one]
  exact hψs

omit [IsTopologicalGroup G] in

private theorem exists_continuous_quotient_monoidHom (N : Subgroup G) {x : G}
    (h : ∃ χ : G →* ℂˣ, Continuous χ ∧ (∀ m ∈ N, χ m = 1) ∧ χ x ≠ 1) :
    ∃ χ : G ⧸ N →* ℂˣ, Continuous χ ∧ χ (x : G ⧸ N) ≠ 1 := by
  obtain ⟨χ₀, hc, hN, hx⟩ := h
  refine ⟨QuotientGroup.lift N χ₀ (fun m hm => hN m hm), ?_, by simpa using hx⟩
  exact (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr hc

end Assembly

end IdeleClassSeparation
end

section
open NumberField NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem Complex Filter Topology

namespace IdeleClassSeparation

variable (K : Type*) [Field K]

private abbrev ArchCoord := (InfinitePlace K → ℝ) × (InfinitePlace K → ℝ)

private noncomputable def archExp (v : ArchCoord K) : InfinitePlace K → ℂ :=
  fun w => Complex.exp (v.1 w + v.2 w * I)

variable {K}

private theorem archExp_add (v v' : ArchCoord K) (w : InfinitePlace K) :
    archExp K (v + v') w = archExp K v w * archExp K v' w := by
  simp only [archExp, Prod.fst_add, Prod.snd_add, Pi.add_apply, ofReal_add, ← Complex.exp_add]
  congr 1; ring

private theorem archExp_zero (w : InfinitePlace K) : archExp K 0 w = 1 := by
  simp [archExp]

private theorem archExp_neg (v : ArchCoord K) (w : InfinitePlace K) :
    archExp K (-v) w = (archExp K v w)⁻¹ := by
  simp only [archExp, Prod.fst_neg, Prod.snd_neg, Pi.neg_apply, ofReal_neg, ← Complex.exp_neg]
  congr 1; ring

private theorem norm_archExp_apply (v : ArchCoord K) (w : InfinitePlace K) :
    ‖archExp K v w‖ = Real.exp (v.1 w) := by
  simp [archExp, Complex.norm_exp]

variable (K)

private noncomputable def unitLogLattice : AddSubgroup (ArchCoord K) where
  carrier := {v | ∃ ε : (𝓞 K)ˣ, ∀ w : InfinitePlace K, archExp K v w = w.embedding (ε : K)}
  zero_mem' := ⟨1, fun w => by simp [archExp_zero]⟩
  add_mem' := by
    rintro v v' ⟨ε, hε⟩ ⟨ε', hε'⟩
    exact ⟨ε * ε', fun w => by rw [archExp_add, hε w, hε' w, coe_mul, map_mul]⟩
  neg_mem' := by
    rintro v ⟨ε, hε⟩
    refine ⟨ε⁻¹, fun w => ?_⟩
    rw [archExp_neg, hε w]
    apply inv_eq_of_mul_eq_one_right
    rw [← map_mul, ← coe_mul, mul_inv_cancel, coe_one, map_one]

variable {K}

private theorem mem_unitLogLattice {v : ArchCoord K} :
    v ∈ unitLogLattice K ↔ ∃ ε : (𝓞 K)ˣ, ∀ w : InfinitePlace K, archExp K v w = w.embedding (ε : K) :=
  Iff.rfl

private theorem place_apply_eq_exp {v : ArchCoord K} {ε : (𝓞 K)ˣ}
    (hε : ∀ w : InfinitePlace K, archExp K v w = w.embedding (ε : K)) (w : InfinitePlace K) :
    w (ε : K) = Real.exp (v.1 w) := by
  rw [← norm_embedding_eq, ← hε w, norm_archExp_apply]

variable (K) [NumberField K]

private theorem exists_nhds_fst_eq_zero :
    ∃ U ∈ 𝓝 (0 : InfinitePlace K → ℝ), ∀ γ ∈ unitLogLattice K, γ.1 ∈ U → γ.1 = 0 := by
  classical

  obtain ⟨W, hWopen, hW⟩ := isOpen_induced_iff.1 (isOpen_discrete ({0} : Set (unitLattice K)))
  have hW0 : (0 : logSpace K) ∈ W := by
    have : ((0 : unitLattice K) : logSpace K) ∈ W := by
      change (0 : unitLattice K) ∈ Subtype.val ⁻¹' W
      rw [hW]; rfl
    simpa using this

  let L : (InfinitePlace K → ℝ) → logSpace K := fun a w' => (mult w'.1 : ℝ) * a w'.1
  have hL : Continuous L := continuous_pi fun w' => continuous_const.mul (continuous_apply w'.1)
  have hL0 : L 0 = 0 := by funext w'; simp [L]
  refine ⟨L ⁻¹' W, hL.continuousAt.preimage_mem_nhds (hWopen.mem_nhds (by rw [hL0]; exact hW0)),
    ?_⟩
  rintro γ ⟨ε, hε⟩ hγ

  have hlog : logEmbedding K (Additive.ofMul ε) = L γ.1 := by
    funext w'
    rw [logEmbedding_component, place_apply_eq_exp hε, Real.log_exp]
  have hmem : logEmbedding K (Additive.ofMul ε) ∈ unitLattice K :=
    ⟨Additive.ofMul ε, trivial, rfl⟩
  have hzero : logEmbedding K (Additive.ofMul ε) = 0 := by
    have h1 : (⟨_, hmem⟩ : unitLattice K) ∈ Subtype.val ⁻¹' W := by
      show logEmbedding K (Additive.ofMul ε) ∈ W
      rw [hlog]; exact hγ
    rw [hW] at h1
    simpa using congrArg Subtype.val h1
  have htors : ε ∈ torsion K := logEmbedding_eq_zero_iff.1 hzero
  funext w
  have h1 : Real.exp (γ.1 w) = 1 := by
    rw [← place_apply_eq_exp hε w]
    exact (mem_torsion K).1 htors w
  simpa using Real.exp_eq_one_iff _ |>.1 h1

private theorem exists_nhds_snd_eq_zero :
    ∃ U ∈ 𝓝 (0 : InfinitePlace K → ℝ), ∀ γ ∈ unitLogLattice K, γ.1 = 0 → γ.2 ∈ U → γ.2 = 0 := by
  classical
  obtain ⟨w₁⟩ := (inferInstance : Nonempty (InfinitePlace K))

  let S : Set ℂ := (fun ζ : torsion K => w₁.embedding ((ζ : (𝓞 K)ˣ) : K)) '' {ζ | ζ ≠ 1}
  have hSfin : S.Finite := (Set.toFinite _).image _
  have h1S : (1 : ℂ) ∉ S := by
    rintro ⟨ζ, hζ, hζ1⟩
    apply hζ
    have hζ1' : w₁.embedding ((ζ : (𝓞 K)ˣ) : K) = 1 := hζ1
    have h : ((ζ : (𝓞 K)ˣ) : K) = ((1 : (𝓞 K)ˣ) : K) := by
      rw [coe_one]; exact w₁.embedding.injective (by rw [hζ1', map_one])
    exact Subtype.ext (coe_injective K h)
  have hN : Sᶜ ∈ 𝓝 (1 : ℂ) := hSfin.isClosed.isOpen_compl.mem_nhds h1S

  let f : (InfinitePlace K → ℝ) → ℂ := fun θ => Complex.exp (θ w₁ * I)
  have hf : Continuous f :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp (continuous_apply w₁)).mul
      continuous_const)
  have hf0 : f 0 = 1 := by simp [f]
  have hU₁ : f ⁻¹' Sᶜ ∈ 𝓝 (0 : InfinitePlace K → ℝ) :=
    hf.continuousAt.preimage_mem_nhds (by rw [hf0]; exact hN)
  have hU₂ : ∀ᶠ θ : InfinitePlace K → ℝ in 𝓝 0, ∀ w, θ w ∈ Metric.ball (0 : ℝ) 1 :=
    eventually_all.2 fun w =>
      (continuous_apply w).continuousAt.preimage_mem_nhds
        (by simpa using Metric.ball_mem_nhds (0 : ℝ) one_pos)
  refine ⟨_, inter_mem hU₁ hU₂, ?_⟩
  rintro γ ⟨ε, hε⟩ hγ1 ⟨hγN, hγball⟩

  have htors : ε ∈ torsion K := (mem_torsion K).2 fun w => by
    rw [place_apply_eq_exp hε w, hγ1]; simp

  have hexp : ∀ w, archExp K γ w = Complex.exp (γ.2 w * I) := fun w => by
    simp [archExp, hγ1]
  have hε1 : ε = 1 := by
    by_contra hne
    apply hγN
    refine ⟨⟨ε, htors⟩, fun h => hne (congrArg Subtype.val h), ?_⟩
    change w₁.embedding (ε : K) = f γ.2
    rw [← hε w₁, hexp w₁]

  funext w
  have h1 : Complex.exp (γ.2 w * I) = 1 := by
    rw [← hexp w, hε w, hε1, coe_one, map_one]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h1
  have hre : γ.2 w = n * (2 * Real.pi) := by
    have := congrArg Complex.im hn
    simpa using this
  have hsmall : |γ.2 w| < 1 := by simpa using hγball w
  have hn0 : n = 0 := by
    by_contra hn0
    have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn0
    rw [hre, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hsmall
    nlinarith [Real.pi_gt_three]
  simp [hre, hn0]

end IdeleClassSeparation
end

section
open NumberField Complex

namespace IdeleClassSeparation

variable (K : Type) [Field K] [NumberField K]

private noncomputable def archValue (w : InfinitePlace K) (y : (AdeleRing (𝓞 K) K)ˣ) : ℂ :=
  InfinitePlace.Completion.extensionEmbedding w ((y : AdeleRing (𝓞 K) K).1 w)

variable {K}

private theorem archValue_one (w : InfinitePlace K) : archValue K w 1 = 1 := by
  unfold archValue
  rw [show ((1 : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w = 1 from rfl, map_one]

private theorem archValue_mul (w : InfinitePlace K) (y z : (AdeleRing (𝓞 K) K)ˣ) :
    archValue K w (y * z) = archValue K w y * archValue K w z := by
  unfold archValue
  rw [show ((y * z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w
      = (y : AdeleRing (𝓞 K) K).1 w * (z : AdeleRing (𝓞 K) K).1 w from rfl, map_mul]

private theorem archValue_ne_zero (w : InfinitePlace K) (y : (AdeleRing (𝓞 K) K)ˣ) : archValue K w y ≠ 0 := by
  intro h
  have h1 : archValue K w y * archValue K w y⁻¹ = 1 := by
    rw [← archValue_mul, mul_inv_cancel, archValue_one]
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

private theorem norm_archValue_pos (w : InfinitePlace K) (y : (AdeleRing (𝓞 K) K)ˣ) : 0 < ‖archValue K w y‖ :=
  norm_pos_iff.mpr (archValue_ne_zero w y)

private theorem continuous_archValue (w : InfinitePlace K) : Continuous (archValue K w) :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
    ((continuous_apply w).comp (continuous_fst.comp Units.continuous_val))

private theorem archValue_eq_one_of_fst_eq_one {y : (AdeleRing (𝓞 K) K)ˣ} (hy : (y : AdeleRing (𝓞 K) K).1 = 1)
    (w : InfinitePlace K) : archValue K w y = 1 := by
  simp only [archValue, hy]
  exact map_one _

variable (K)

private noncomputable def archCharFn (c : InfinitePlace K → ℝ) (n : InfinitePlace K → ℤ)
    (y : (AdeleRing (𝓞 K) K)ˣ) : ℂ :=
  ∏ w : InfinitePlace K,
    exp (I * (c w * Real.log ‖archValue K w y‖)) * (archValue K w y / (‖archValue K w y‖ : ℂ)) ^ (n w)

variable {K}

private theorem archCharFn_one (c : InfinitePlace K → ℝ) (n : InfinitePlace K → ℤ) : archCharFn K c n 1 = 1 := by
  simp [archCharFn, archValue_one]

private theorem archCharFn_mul (c : InfinitePlace K → ℝ) (n : InfinitePlace K → ℤ) (y z : (AdeleRing (𝓞 K) K)ˣ) :
    archCharFn K c n (y * z) = archCharFn K c n y * archCharFn K c n z := by
  unfold archCharFn
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hy := norm_archValue_pos w y
  have hz := norm_archValue_pos w z
  rw [archValue_mul, norm_mul, Real.log_mul hy.ne' hz.ne', Complex.ofReal_mul, mul_div_mul_comm, mul_zpow]
  push_cast
  rw [mul_add, mul_add, Complex.exp_add]
  ring

private theorem archCharFn_ne_zero (c : InfinitePlace K → ℝ) (n : InfinitePlace K → ℤ) (y : (AdeleRing (𝓞 K) K)ˣ) :
    archCharFn K c n y ≠ 0 := by
  unfold archCharFn
  refine Finset.prod_ne_zero_iff.mpr fun w _ => mul_ne_zero (Complex.exp_ne_zero _) (zpow_ne_zero _ ?_)
  exact div_ne_zero (archValue_ne_zero w y) (by exact_mod_cast (norm_archValue_pos w y).ne')

private theorem continuous_archCharFactor (c : InfinitePlace K → ℝ) (n : InfinitePlace K → ℤ) (w : InfinitePlace K) :
    Continuous fun y : (AdeleRing (𝓞 K) K)ˣ =>
      exp (I * (c w * Real.log ‖archValue K w y‖)) * (archValue K w y / (‖archValue K w y‖ : ℂ)) ^ (n w) := by
  refine Continuous.mul ?_ ?_
  · refine Complex.continuous_exp.comp (continuous_const.mul (continuous_const.mul ?_))
    exact Complex.continuous_ofReal.comp
      ((continuous_norm.comp (continuous_archValue w)).log fun y => (norm_archValue_pos w y).ne')
  · refine Continuous.zpow₀ ?_ (n w) fun y => Or.inl ?_
    · refine (continuous_archValue w).div
        (Complex.continuous_ofReal.comp (continuous_norm.comp (continuous_archValue w))) fun y => ?_
      exact_mod_cast (norm_archValue_pos w y).ne'
    · exact div_ne_zero (archValue_ne_zero w y) (by exact_mod_cast (norm_archValue_pos w y).ne')

private theorem continuous_archCharFn (c : InfinitePlace K → ℝ) (n : InfinitePlace K → ℤ) :
    Continuous (archCharFn K c n) := by
  unfold archCharFn
  have h := continuous_archCharFactor c n
  fun_prop

variable (K)

private noncomputable def archChar (c : InfinitePlace K → ℝ) (n : InfinitePlace K → ℤ) : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ :=
  MonoidHom.toHomUnits
    { toFun := archCharFn K c n
      map_one' := archCharFn_one c n
      map_mul' := archCharFn_mul c n }

variable {K}

private theorem archChar_apply_val (c : InfinitePlace K → ℝ) (n : InfinitePlace K → ℤ) (y : (AdeleRing (𝓞 K) K)ˣ) :
    ((archChar K c n y : ℂˣ) : ℂ) = archCharFn K c n y := rfl

private theorem continuous_archChar (c : InfinitePlace K → ℝ) (n : InfinitePlace K → ℤ) :
    Continuous (archChar K c n) := by
  refine Units.continuous_iff.mpr ⟨continuous_archCharFn c n, ?_⟩
  have : (fun y : (AdeleRing (𝓞 K) K)ˣ => (((archChar K c n y : ℂˣ)⁻¹ : ℂˣ) : ℂ))
      = fun y => archCharFn K c n y⁻¹ := by
    funext y
    rw [← map_inv, archChar_apply_val]
  rw [this]
  exact (continuous_archCharFn c n).comp continuous_inv

private theorem archChar_eq_one_of_fst_eq_one (c : InfinitePlace K → ℝ) (n : InfinitePlace K → ℤ)
    {y : (AdeleRing (𝓞 K) K)ˣ} (hy : (y : AdeleRing (𝓞 K) K).1 = 1) : archChar K c n y = 1 := by
  apply Units.ext
  rw [archChar_apply_val, Units.val_one]
  unfold archCharFn
  refine Finset.prod_eq_one fun w _ => ?_
  simp [archValue_eq_one_of_fst_eq_one hy w]

private theorem archChar_apply_eq_exp (c : InfinitePlace K → ℝ) (n : InfinitePlace K → ℤ) (y : (AdeleRing (𝓞 K) K)ˣ) :
    ((archChar K c n y : ℂˣ) : ℂ)
      = exp (I * ((∑ w, (c w : ℂ) * Real.log ‖archValue K w y‖) + ∑ w, (n w : ℂ) * arg (archValue K w y))) := by
  rw [archChar_apply_val]
  unfold archCharFn
  rw [← Finset.sum_add_distrib, Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hz := archValue_ne_zero w y
  have hdiv : archValue K w y / (‖archValue K w y‖ : ℂ) = exp ((arg (archValue K w y) : ℂ) * I) := by
    have h := Complex.norm_mul_exp_arg_mul_I (archValue K w y)
    rw [div_eq_iff (by exact_mod_cast (norm_archValue_pos w y).ne')]
    conv_lhs => rw [← h]
    ring
  rw [hdiv, ← Complex.exp_int_mul, ← Complex.exp_add]
  congr 1
  ring

section ArchCoordinates

open scoped Classical

variable (K)

private noncomputable def archCoord (y : (AdeleRing (𝓞 K) K)ˣ) : ArchCoord K :=
  (fun w => Real.log ‖archValue K w y‖, fun w => arg (archValue K w y))

private theorem archExp_archCoord (y : (AdeleRing (𝓞 K) K)ˣ) (w : InfinitePlace K) :
    archExp K (archCoord K y) w = archValue K w y := by
  simp only [archExp, archCoord]
  rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log (norm_archValue_pos w y)]
  exact Complex.norm_mul_exp_arg_mul_I _

private noncomputable def argPeriod (w : InfinitePlace K) : ArchCoord K := (0, Pi.single w (2 * Real.pi))

omit [NumberField K] in
private theorem archExp_argPeriod (w w' : InfinitePlace K) : archExp K (argPeriod K w) w' = 1 := by
  simp only [archExp, argPeriod, Pi.zero_apply, Complex.ofReal_zero, zero_add]
  by_cases h : w = w'
  · subst h
    simp only [Pi.single_eq_same]
    rw [show ((2 * Real.pi : ℝ) : ℂ) * I = 2 * Real.pi * I by push_cast; ring]
    exact Complex.exp_two_pi_mul_I
  · rw [Pi.single_eq_of_ne (Ne.symm h)]
    simp

private theorem archValue_map_algebraMap (w : InfinitePlace K) (u : Kˣ) :
    archValue K w (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) = w.embedding u :=
  InfinitePlace.Completion.extensionEmbedding_coe w _

variable {K}

private theorem linearMap_apply_eq_sum (ℓ : ArchCoord K →ₗ[ℝ] ℝ) (v : ArchCoord K) :
    ℓ v = (∑ w, v.1 w * ℓ (Pi.single w 1, 0)) + ∑ w, v.2 w * ℓ (0, Pi.single w 1) := by
  have hsingle : ∀ (f : InfinitePlace K → ℝ) (w : InfinitePlace K),
      (Pi.single w (f w) : InfinitePlace K → ℝ) = f w • (Pi.single w (1 : ℝ) : InfinitePlace K → ℝ) := by
    intro f w
    ext j
    by_cases h : j = w <;> simp [Pi.single_apply, h]
  have h1 : (∑ w, v.1 w • (Pi.single w (1 : ℝ) : InfinitePlace K → ℝ)) = v.1 := by
    conv_rhs => rw [← Finset.univ_sum_single v.1]
    exact Finset.sum_congr rfl fun w _ => (hsingle v.1 w).symm
  have h2 : (∑ w, v.2 w • (Pi.single w (1 : ℝ) : InfinitePlace K → ℝ)) = v.2 := by
    conv_rhs => rw [← Finset.univ_sum_single v.2]
    exact Finset.sum_congr rfl fun w _ => (hsingle v.2 w).symm
  have hv : v = (∑ w, v.1 w • ((Pi.single w (1 : ℝ) : InfinitePlace K → ℝ), (0 : InfinitePlace K → ℝ))) +
      ∑ w, v.2 w • ((0 : InfinitePlace K → ℝ), (Pi.single w (1 : ℝ) : InfinitePlace K → ℝ)) := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.fst_sum, Prod.smul_fst, smul_zero, Finset.sum_const_zero, add_zero, h1]
    · simp only [Prod.snd_add, Prod.snd_sum, Prod.smul_snd, smul_zero, Finset.sum_const_zero, zero_add, h2]
  conv_lhs => rw [hv]
  simp only [map_add, map_sum, map_smul, smul_eq_mul]

private theorem exists_archChar_eq_exp_linearMap (ℓ : ArchCoord K →ₗ[ℝ] ℝ)
    (hℓ : ∀ w : InfinitePlace K, ∃ n : ℤ, ℓ (argPeriod K w) = n) :
    ∃ (c : InfinitePlace K → ℝ) (n : InfinitePlace K → ℤ), ∀ y : (AdeleRing (𝓞 K) K)ˣ,
      ((archChar K c n y : ℂˣ) : ℂ) = exp (2 * Real.pi * I * ℓ (archCoord K y)) := by
  choose n hn using hℓ
  refine ⟨fun w => 2 * Real.pi * ℓ (Pi.single w 1, 0), n, fun y => ?_⟩
  have hper : ∀ w, (n w : ℝ) = 2 * Real.pi * ℓ (0, Pi.single w 1) := by
    intro w
    have h2 : argPeriod K w =
        (2 * Real.pi) • (((0 : InfinitePlace K → ℝ), (Pi.single w (1 : ℝ) : InfinitePlace K → ℝ)) : ArchCoord K) := by
      ext w'
      · simp [argPeriod]
      · simp only [argPeriod, Prod.smul_snd, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
        split_ifs <;> simp
    rw [← hn w, h2, map_smul, smul_eq_mul]
  rw [archChar_apply_eq_exp, linearMap_apply_eq_sum]
  congr 1
  have hn' : ∀ w, (n w : ℂ) = 2 * Real.pi * (ℓ (0, Pi.single w 1) : ℂ) := fun w => by
    rw [← Complex.ofReal_intCast, hper w]; push_cast; ring
  simp only [archCoord, hn']
  push_cast
  simp only [Finset.mul_sum, mul_add]
  congr 1 <;> refine Finset.sum_congr rfl fun w _ => ?_ <;> ring

end ArchCoordinates

end IdeleClassSeparation
end

section
open NumberField IsDedekindDomain

namespace IdeleClassSeparation

variable (F : Type) [Field F] [NumberField F]

private def finComp (x : (AdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) : v.adicCompletion F :=
  (x : AdeleRing (𝓞 F) F).2 v

variable {F}

private theorem finComp_mul (x y : (AdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    finComp F (x * y) v = finComp F x v * finComp F y v := rfl

private theorem finComp_one (v : HeightOneSpectrum (𝓞 F)) : finComp F 1 v = 1 := rfl

private theorem finComp_mul_finComp_inv (x : (AdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    finComp F x v * finComp F x⁻¹ v = 1 := by
  rw [← finComp_mul, mul_inv_cancel, finComp_one]

private theorem finComp_inv (x : (AdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    finComp F x⁻¹ v = (finComp F x v)⁻¹ :=
  eq_inv_of_mul_eq_one_right (finComp_mul_finComp_inv x v)

private theorem finComp_ne_zero (x : (AdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) : finComp F x v ≠ 0 :=
  left_ne_zero_of_mul_eq_one (finComp_mul_finComp_inv x v)

private theorem fst_mul' (a b : AdeleRing (𝓞 F) F) : (a * b).1 = a.1 * b.1 := rfl

private theorem fst_one' : ((1 : AdeleRing (𝓞 F) F)).1 = 1 := rfl

variable (F)

private def unitBox : Subgroup (AdeleRing (𝓞 F) F)ˣ where
  carrier := {x | ∀ v : HeightOneSpectrum (𝓞 F),
    finComp F x v ∈ v.adicCompletionIntegers F ∧ finComp F x⁻¹ v ∈ v.adicCompletionIntegers F}
  one_mem' := fun v => by simp [finComp_one]
  mul_mem' := by
    intro x y hx hy v
    refine ⟨?_, ?_⟩
    · rw [finComp_mul]; exact mul_mem (hx v).1 (hy v).1
    · rw [mul_inv_rev, finComp_mul]; exact mul_mem (hy v).2 (hx v).2
  inv_mem' := by
    intro x hx v
    rw [inv_inv]
    exact ⟨(hx v).2, (hx v).1⟩

variable {F}

private theorem mem_unitBox {x : (AdeleRing (𝓞 F) F)ˣ} : x ∈ unitBox F ↔ ∀ v : HeightOneSpectrum (𝓞 F),
    finComp F x v ∈ v.adicCompletionIntegers F ∧ finComp F x⁻¹ v ∈ v.adicCompletionIntegers F :=
  Iff.rfl

private theorem valuation_finComp_eq_one {x : (AdeleRing (𝓞 F) F)ˣ} (hx : x ∈ unitBox F)
    (v : HeightOneSpectrum (𝓞 F)) : Valued.v (finComp F x v) = 1 := by
  have h1 : Valued.v (finComp F x v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hx v).1
  have h2 : Valued.v (finComp F x⁻¹ v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hx v).2
  rw [finComp_inv, map_inv₀] at h2
  have hpos : 0 < Valued.v (finComp F x v) := (Valuation.pos_iff _).mpr (finComp_ne_zero x v)
  exact le_antisymm h1 ((inv_le_one₀ hpos).mp h2)

private theorem continuous_finComp (v : HeightOneSpectrum (𝓞 F)) : Continuous (fun x => finComp F x v) :=
  (RestrictedProduct.continuous_eval v).comp (continuous_snd.comp Units.continuous_val)

private theorem continuous_finComp_inv (v : HeightOneSpectrum (𝓞 F)) : Continuous (fun x => finComp F x⁻¹ v) :=
  (RestrictedProduct.continuous_eval v).comp (continuous_snd.comp Units.continuous_coe_inv)

variable (F)

private theorem isOpen_unitBox : IsOpen (unitBox F : Set (AdeleRing (𝓞 F) F)ˣ) := by
  have hO : IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), v ∉ (∅ : Set _) →
      a.1 v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_imp_mem fun v => Valued.isOpen_valuationSubring _
  have h1 : Continuous fun a : (AdeleRing (𝓞 F) F)ˣ => (a : AdeleRing (𝓞 F) F).2 :=
    continuous_snd.comp Units.continuous_val
  have h2 : Continuous fun a : (AdeleRing (𝓞 F) F)ˣ => ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 :=
    continuous_snd.comp Units.continuous_coe_inv
  have hset : (unitBox F : Set (AdeleRing (𝓞 F) F)ˣ) =
      (fun a : (AdeleRing (𝓞 F) F)ˣ => (a : AdeleRing (𝓞 F) F).2) ⁻¹' {a | ∀ v, v ∉ (∅ : Set _) →
          a.1 v ∈ v.adicCompletionIntegers F} ∩
        (fun a : (AdeleRing (𝓞 F) F)ˣ => ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2) ⁻¹'
          {a | ∀ v, v ∉ (∅ : Set _) → a.1 v ∈ v.adicCompletionIntegers F} := by
    ext x
    simp only [SetLike.mem_coe, mem_unitBox, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq,
      Set.mem_empty_iff_false, not_false_eq_true, true_implies]
    exact ⟨fun h => ⟨fun v => (h v).1, fun v => (h v).2⟩, fun h v => ⟨h.1 v, h.2 v⟩⟩
  rw [hset]
  exact (hO.preimage h1).inter (hO.preimage h2)

private def ballBox (v₀ : HeightOneSpectrum (𝓞 F)) (r : v₀.adicCompletion F) (hr : r ≠ 0) :
    Subgroup (AdeleRing (𝓞 F) F)ˣ where
  carrier := {x | x ∈ unitBox F ∧ Valued.v (finComp F x v₀ - 1) < Valued.v r}
  one_mem' := ⟨(unitBox F).one_mem, by simpa [finComp_one] using (Valuation.pos_iff _).mpr hr⟩
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨(unitBox F).mul_mem hx hy, ?_⟩
    have hxy : finComp F (x * y) v₀ - 1 = finComp F x v₀ * (finComp F y v₀ - 1) + (finComp F x v₀ - 1) := by
      rw [finComp_mul]; ring
    rw [hxy]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ hx')
    rw [Valuation.map_mul, valuation_finComp_eq_one hx, one_mul]
    exact hy'
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    refine ⟨(unitBox F).inv_mem hx, ?_⟩
    have h : finComp F x⁻¹ v₀ - 1 = finComp F x⁻¹ v₀ * (1 - finComp F x v₀) := by
      rw [mul_sub, mul_one, finComp_inv, inv_mul_cancel₀ (finComp_ne_zero x v₀)]
    rw [h, Valuation.map_mul, valuation_finComp_eq_one ((unitBox F).inv_mem hx), one_mul, ← Valuation.map_neg,
      neg_sub]
    exact hx'

private theorem ballBox_le_unitBox (v₀ : HeightOneSpectrum (𝓞 F)) (r : v₀.adicCompletion F) (hr : r ≠ 0) :
    ballBox F v₀ r hr ≤ unitBox F := fun _ hx => hx.1

private theorem isOpen_ballBox (v₀ : HeightOneSpectrum (𝓞 F)) (r : v₀.adicCompletion F) (hr : r ≠ 0) :
    IsOpen (ballBox F v₀ r hr : Set (AdeleRing (𝓞 F) F)ˣ) := by
  have hball : IsOpen {z : v₀.adicCompletion F | Valued.v (z - 1) < Valued.v r} := by
    have h := (Valued.isOpen_ball (R := v₀.adicCompletion F) (Valued.v.restrict r)).preimage
      (continuous_sub_right (1 : v₀.adicCompletion F))
    convert h using 1
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Valuation.restrict_lt_iff]
  have hset : (ballBox F v₀ r hr : Set (AdeleRing (𝓞 F) F)ˣ) =
      (unitBox F : Set (AdeleRing (𝓞 F) F)ˣ) ∩ (fun x => finComp F x v₀) ⁻¹' {z | Valued.v (z - 1) < Valued.v r} :=
    rfl
  rw [hset]
  exact (isOpen_unitBox F).inter (hball.preimage (continuous_finComp v₀))

private noncomputable def principal : Fˣ →* (AdeleRing (𝓞 F) F)ˣ := Units.map (algebraMap F (AdeleRing (𝓞 F) F))

variable {F}

private theorem finComp_principal (u : Fˣ) (v : HeightOneSpectrum (𝓞 F)) :
    finComp F (principal F u) v = ((u : F) : v.adicCompletion F) := rfl

private theorem fst_principal (u : Fˣ) (w : InfinitePlace F) :
    ((principal F u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w = ((u : F) : w.Completion) := rfl

private theorem exists_unit_of_principal_mem_unitBox {u : Fˣ} (hu : principal F u ∈ unitBox F) :
    ∃ ε : (𝓞 F)ˣ, ((ε : 𝓞 F) : F) = u := by
  have hint : ∀ (t : F), (∀ v : HeightOneSpectrum (𝓞 F), ((t : v.adicCompletion F)) ∈ v.adicCompletionIntegers F) →
      ∃ a : 𝓞 F, (a : F) = t := by
    intro t ht
    obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) t fun v => by
      have := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (ht v)
      rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
    exact ⟨a, ha⟩
  obtain ⟨a, ha⟩ := hint u fun v => by simpa [finComp_principal] using (hu v).1
  obtain ⟨b, hb⟩ := hint (u⁻¹ : Fˣ) fun v => by
    have := (hu v).2
    rwa [← map_inv, finComp_principal] at this
  have hab : a * b = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 F) F
    have ha' : algebraMap (𝓞 F) F a = (u : F) := ha
    have hb' : algebraMap (𝓞 F) F b = ((u⁻¹ : Fˣ) : F) := hb
    rw [map_mul, map_one, ha', hb']
    exact u.mul_inv
  exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha⟩

private theorem exists_open_subgroup (x : (AdeleRing (𝓞 F) F)ˣ) (hx : ∀ u : Fˣ, x ≠ principal F u) :
    ∃ S : Subgroup (AdeleRing (𝓞 F) F)ˣ, IsOpen (S : Set (AdeleRing (𝓞 F) F)ˣ) ∧ S ≤ unitBox F ∧
      ∀ u : Fˣ, x * (principal F u)⁻¹ ∈ S →
        ((x * (principal F u)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 ≠ 1 := by

  have harch : ∀ u : Fˣ, ((x * (principal F u)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 →
      (x : AdeleRing (𝓞 F) F).1 = ((principal F u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 := by
    intro u h
    have h' : ((x * (principal F u)⁻¹ * principal F u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 =
        (x : AdeleRing (𝓞 F) F).1 := by rw [inv_mul_cancel_right]
    rw [Units.val_mul, fst_mul', h, one_mul] at h'
    exact h'.symm
  by_cases hex : ∃ u₀ : Fˣ, (x : AdeleRing (𝓞 F) F).1 = ((principal F u₀ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1
  · obtain ⟨u₀, hu₀⟩ := hex

    set y : (AdeleRing (𝓞 F) F)ˣ := x * (principal F u₀)⁻¹ with hy_def
    have hy1 : y ≠ 1 := by
      intro h
      apply hx u₀
      rw [← mul_inv_eq_one.mp h]
    have hyarch : (y : AdeleRing (𝓞 F) F).1 = 1 := by
      rw [hy_def, Units.val_mul, fst_mul', hu₀, ← fst_mul', ← Units.val_mul, mul_inv_cancel, Units.val_one, fst_one']
    have hyfin : ∃ v₀ : HeightOneSpectrum (𝓞 F), finComp F y v₀ ≠ 1 := by
      by_contra hcon
      apply hy1
      apply Units.ext
      refine Prod.ext hyarch ?_
      exact RestrictedProduct.ext _ _ fun v => by_contra fun h => hcon ⟨v, h⟩
    obtain ⟨v₀, hv₀⟩ := hyfin
    have hr : finComp F y v₀ - 1 ≠ 0 := sub_ne_zero.mpr hv₀
    refine ⟨ballBox F v₀ _ hr, isOpen_ballBox F v₀ _ hr, ballBox_le_unitBox F v₀ _ hr, ?_⟩
    intro u hu h1

    have huu₀ : u = u₀ := by
      have h2 := (harch u h1).symm.trans hu₀
      obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
      have h3 := congrArg (fun a => a w) h2
      simp only [fst_principal] at h3
      exact Units.ext ((WithAbs.equiv w.1).symm.injective (UniformSpace.Completion.coe_injective (WithAbs w.1)
        (congrArg NumberField.InfinitePlace.Completion.toCompletion h3)))
    subst huu₀
    exact lt_irrefl _ hu.2
  · exact ⟨unitBox F, isOpen_unitBox F, le_rfl, fun u _ h => hex ⟨u, harch u h⟩⟩

end IdeleClassSeparation
end

section Assembly

open NumberField IsDedekindDomain Complex

namespace IdeleClassSeparation

variable {F : Type} [Field F] [NumberField F]

private theorem fst_eq_one_of_forall_archValue_eq_one {z : (AdeleRing (𝓞 F) F)ˣ}
    (h : ∀ w : InfinitePlace F, archValue F w z = 1) : ((z : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 := by
  funext w
  exact (InfinitePlace.Completion.extensionEmbedding w).injective ((h w).trans (map_one _).symm)

private theorem archValue_inv (w : InfinitePlace F) (y : (AdeleRing (𝓞 F) F)ˣ) :
    archValue F w y⁻¹ = (archValue F w y)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← archValue_mul, inv_mul_cancel, archValue_one])

variable (F)

private noncomputable def archLattice (S : Subgroup (AdeleRing (𝓞 F) F)ˣ) : AddSubgroup (ArchCoord F) where
  carrier := {v | ∃ u : Fˣ, principal F u ∈ S ∧ ∀ w : InfinitePlace F, archExp F v w = archValue F w (principal F u)}
  zero_mem' := ⟨1, by rw [map_one]; exact S.one_mem, fun w => by rw [archExp_zero, map_one, archValue_one]⟩
  add_mem' := by
    rintro v v' ⟨u, hu, h⟩ ⟨u', hu', h'⟩
    refine ⟨u * u', by rw [map_mul]; exact S.mul_mem hu hu', fun w => ?_⟩
    rw [archExp_add, h w, h' w, map_mul, archValue_mul]
  neg_mem' := by
    rintro v ⟨u, hu, h⟩
    refine ⟨u⁻¹, by rw [map_inv]; exact S.inv_mem hu, fun w => ?_⟩
    rw [archExp_neg, h w, map_inv, archValue_inv]

variable {F}

private theorem mem_archLattice {S : Subgroup (AdeleRing (𝓞 F) F)ˣ} {v : ArchCoord F} :
    v ∈ archLattice F S ↔
      ∃ u : Fˣ, principal F u ∈ S ∧ ∀ w : InfinitePlace F, archExp F v w = archValue F w (principal F u) :=
  Iff.rfl

private theorem archValue_principal (w : InfinitePlace F) (u : Fˣ) : archValue F w (principal F u) = w.embedding u :=
  archValue_map_algebraMap F w u

private theorem archLattice_le_unitLogLattice {S : Subgroup (AdeleRing (𝓞 F) F)ˣ} (hS : S ≤ unitBox F) :
    ∀ v ∈ archLattice F S, v ∈ unitLogLattice F := by
  rintro v ⟨u, hu, h⟩
  obtain ⟨ε, hε⟩ := exists_unit_of_principal_mem_unitBox (hS hu)
  refine (mem_unitLogLattice).2 ⟨ε, fun w => ?_⟩
  rw [h w, archValue_principal]
  exact congrArg w.embedding (hε.symm.trans rfl)

private theorem discreteTopology_archLattice {S : Subgroup (AdeleRing (𝓞 F) F)ˣ} (hS : S ≤ unitBox F) :
    DiscreteTopology (archLattice F S) := by
  obtain ⟨U₁, hU₁, h₁⟩ := exists_nhds_fst_eq_zero F
  obtain ⟨U₂, hU₂, h₂⟩ := exists_nhds_snd_eq_zero F
  exact discreteTopology_prod_of_isolated (archLattice F S)
    ⟨U₁, hU₁, fun γ hγ => h₁ γ (archLattice_le_unitLogLattice hS γ hγ)⟩
    ⟨U₂, hU₂, fun γ hγ => h₂ γ (archLattice_le_unitLogLattice hS γ hγ)⟩

private theorem argPeriod_mem_archLattice (S : Subgroup (AdeleRing (𝓞 F) F)ˣ) (w : InfinitePlace F) :
    argPeriod F w ∈ archLattice F S :=
  ⟨1, by rw [map_one]; exact S.one_mem, fun w' => by rw [archExp_argPeriod, map_one, archValue_one]⟩

private theorem archCoord_principal_mem_archLattice {S : Subgroup (AdeleRing (𝓞 F) F)ˣ} {u : Fˣ}
    (hu : principal F u ∈ S) :
    archCoord F (principal F u) ∈ archLattice F S :=
  ⟨u, hu, fun w => archExp_archCoord F (principal F u) w⟩

private theorem exists_linearMap_int_on_archLattice {S : Subgroup (AdeleRing (𝓞 F) F)ˣ} (hS : S ≤ unitBox F)
    {v : ArchCoord F} (hv : v ∉ archLattice F S) :
    ∃ ℓ : ArchCoord F →ₗ[ℝ] ℝ, (∀ g ∈ archLattice F S, ∃ n : ℤ, ℓ g = n) ∧ ∀ n : ℤ, ℓ v ≠ n := by
  haveI : DiscreteTopology (archLattice F S) := discreteTopology_archLattice hS
  haveI : DiscreteTopology (archLattice F S).toIntSubmodule :=
    inferInstanceAs (DiscreteTopology (archLattice F S))
  obtain ⟨ℓ, hℓ, hℓv⟩ := exists_linearMap_int_on_of_discrete (archLattice F S).toIntSubmodule hv
  exact ⟨ℓ, fun g hg => hℓ g hg, hℓv⟩

private theorem two_pi_I_ne_zero : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
  simp [Real.pi_ne_zero, I_ne_zero]

private theorem exists_continuous_char_of_not_principal (y : (AdeleRing (𝓞 F) F)ˣ) (hy : ∀ u : Fˣ, y ≠ principal F u) :
    ∃ χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ,
      Continuous χ ∧ (∀ n ∈ (principal F).range, χ n = 1) ∧ χ y ≠ 1 := by
  obtain ⟨S, hSo, hSle, hSprop⟩ := exists_open_subgroup y hy
  by_cases hsup : y ∈ S ⊔ (principal F).range
  · obtain ⟨s, hs, n, hn, hsn⟩ := Subgroup.mem_sup.1 hsup
    obtain ⟨u₀, rfl⟩ := MonoidHom.mem_range.1 hn
    have hs_eq : s = y * (principal F u₀)⁻¹ := by rw [← hsn, mul_inv_cancel_right]
    have hnot : archCoord F s ∉ archLattice F S := by
      rintro ⟨u, hu, h⟩
      have hrew : y * (principal F (u₀ * u))⁻¹ = s * (principal F u)⁻¹ := by
        rw [hs_eq, map_mul, mul_inv, mul_assoc]
      have hmem : y * (principal F (u₀ * u))⁻¹ ∈ S := by
        rw [hrew]; exact S.mul_mem hs (S.inv_mem hu)
      apply hSprop (u₀ * u) hmem
      apply fst_eq_one_of_forall_archValue_eq_one
      intro w
      rw [hrew, archValue_mul, archValue_inv, ← h w, archExp_archCoord, mul_inv_cancel₀ (archValue_ne_zero w s)]
    obtain ⟨ℓ, hℓΓ, hℓs⟩ := exists_linearMap_int_on_archLattice hSle hnot
    obtain ⟨c, m, hcm⟩ := exists_archChar_eq_exp_linearMap ℓ (fun w => hℓΓ _ (argPeriod_mem_archLattice S w))
    refine exists_continuous_eq_one_on_of_eq_mul (principal F).range S hSo (archChar F c m) (continuous_archChar c m)
      ?_ hs (MonoidHom.mem_range.2 ⟨u₀, rfl⟩) hsn.symm ?_
    · intro g hgS hgN
      obtain ⟨u, rfl⟩ := MonoidHom.mem_range.1 hgN
      obtain ⟨k, hk⟩ := hℓΓ _ (archCoord_principal_mem_archLattice hgS)
      apply Units.ext
      rw [Units.val_one, hcm, hk]
      rw [show (2 * (Real.pi : ℂ) * I * ((k : ℝ) : ℂ)) = (k : ℂ) * (2 * Real.pi * I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I k
    · intro h1
      have hval := congrArg Units.val h1
      rw [Units.val_one, hcm] at hval
      obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 hval
      apply hℓs k
      have hc : ((ℓ (archCoord F s) : ℝ) : ℂ) = (k : ℂ) := by
        apply mul_left_cancel₀ two_pi_I_ne_zero
        rw [hk]; ring
      exact_mod_cast hc
  · exact exists_continuous_eq_one_on_of_notMem_sup (principal F).range S hSo hsup

private theorem solution_general (A : Subgroup (AdeleRing (𝓞 F) F)ˣ) :
    ∀ x : ↥A ⧸ (principal F).range.subgroupOf A, x ≠ 1 →
      ∃ χ : (↥A ⧸ (principal F).range.subgroupOf A) →* ℂˣ, Continuous χ ∧ χ x ≠ 1 := by
  intro x hx
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  have ha : ∀ u : Fˣ, (a : (AdeleRing (𝓞 F) F)ˣ) ≠ principal F u := by
    intro u hau
    apply hx
    rw [QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.2 (MonoidHom.mem_range.2 ⟨u, hau.symm⟩)
  obtain ⟨χ, hχc, hχN, hχa⟩ := exists_continuous_char_of_not_principal (a : (AdeleRing (𝓞 F) F)ˣ) ha
  refine exists_continuous_quotient_monoidHom ((principal F).range.subgroupOf A)
    ⟨χ.comp A.subtype, hχc.comp continuous_subtype_val, ?_, hχa⟩
  intro m hm
  exact hχN _ (Subgroup.mem_subgroupOf.1 hm)

private theorem principalIdeles_eq : M4aHerbrand.principalIdeles (𝓞 F) F = (principal F).range := rfl

end IdeleClassSeparation

end Assembly

open NumberField M4aHerbrand

theorem solution
    (F : Type) [Field F] [NumberField F] :
    ∀ x : ↥(NumberField.TateGlobal.normOneIdeles F) ⧸
        (principalIdeles (𝓞 F) F).subgroupOf (NumberField.TateGlobal.normOneIdeles F),
      x ≠ 1 → ∃ χ : (↥(NumberField.TateGlobal.normOneIdeles F) ⧸
          (principalIdeles (𝓞 F) F).subgroupOf (NumberField.TateGlobal.normOneIdeles F)) →* ℂˣ,
        Continuous χ ∧ χ x ≠ 1 :=
  IdeleClassSeparation.solution_general (NumberField.TateGlobal.normOneIdeles _)

end S_NumberField_TateGlobal_forall_ne_one_exists_continuous_monoidHom_normOneIdeleClass_apply_ne_one
end P2MW
export P2MW.S_NumberField_TateGlobal_forall_ne_one_exists_continuous_monoidHom_normOneIdeleClass_apply_ne_one (solution)
