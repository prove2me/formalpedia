-- Prove2me | solution 1 for LanglandsTunnell.Converse.exists_isJLTwist
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/f87b5961-0561-5eea-9384-d8b302efa5ca

import Definitions.Def_LanglandsTunnell_JLData
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicLevel
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

p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_Converse_exists_isJLTwist

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

end IdeleClassSeparation

end Assembly

section TwistAbstract
open Complex

namespace IdeleClassSeparation

private def circleUnits : Subgroup ℂˣ where
  carrier := {z | ‖((z : ℂˣ) : ℂ)‖ = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, norm_mul] at ha hb ⊢
    rw [ha, hb, mul_one]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [Units.val_inv_eq_inv_val, norm_inv, ha, inv_one]

private theorem mem_circleUnits {z : ℂˣ} : z ∈ circleUnits ↔ ‖((z : ℂˣ) : ℂ)‖ = 1 := Iff.rfl

private theorem circleUnits_divisible : ∀ (a : circleUnits) (n : ℕ), n ≠ 0 → ∃ b : circleUnits, b ^ n = a := by
  intro a n hn
  obtain ⟨b, hb⟩ := forall_exists_pow_eq_units_complex (a : ℂˣ) n hn
  have hbn : ‖((b : ℂˣ) : ℂ)‖ = 1 := by
    have h1 : ‖((b : ℂˣ) : ℂ)‖ ^ n = 1 := by
      rw [← norm_pow, ← Units.val_pow_eq_pow_val, hb]
      exact a.2
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).mp h1
  exact ⟨⟨b, hbn⟩, Subtype.ext (by simpa using hb)⟩

section Join

variable {G A : Type} [CommGroup G] [CommGroup A]

private theorem exists_eq_on_of_eq_one_on_inf (hA : ∀ (a : A) (n : ℕ), n ≠ 0 → ∃ b : A, b ^ n = a)
    (S N : Subgroup G) (ψ : S →* A) (hψN : ∀ s : S, (s : G) ∈ N → ψ s = 1) :
    ∃ χ : G →* A, (∀ s : S, χ s = ψ s) ∧ ∀ m ∈ N, χ m = 1 := by
  let p : S × N →* G := S.subtype.coprod N.subtype
  let Ψ : S × N →* A := ψ.comp (MonoidHom.fst S N)
  have hker : p.ker ≤ Ψ.ker := by
    rintro ⟨a, b⟩ hab
    have hab' : (a : G) * b = 1 := hab
    have haN : (a : G) ∈ N := by
      rw [eq_inv_of_mul_eq_one_left hab']
      exact N.inv_mem b.2
    show ψ a = 1
    exact hψN a haN
  let θ : p.range →* A :=
    (QuotientGroup.lift p.ker Ψ hker).comp (QuotientGroup.quotientKerEquivRange p).symm.toMonoidHom
  have hθ : ∀ q : S × N, θ (p.rangeRestrict q) = Ψ q := by
    intro q
    have h1 : (QuotientGroup.quotientKerEquivRange p) (QuotientGroup.mk q) = p.rangeRestrict q := rfl
    simp only [θ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← h1, MulEquiv.symm_apply_apply,
      QuotientGroup.lift_mk]
  obtain ⟨χ, hχ⟩ := exists_monoidHom_extension hA p.range θ
  refine ⟨χ, fun s => ?_, fun m hm => ?_⟩
  · have h := hχ (p.rangeRestrict (s, 1))
    rw [hθ] at h
    simpa [p, Ψ] using h
  · have h := hχ (p.rangeRestrict (1, ⟨m, hm⟩))
    rw [hθ] at h
    simpa [p, Ψ] using h

private theorem continuous_of_continuousOn_openSubgroup [TopologicalSpace G] [IsTopologicalGroup G] (χ : G →* ℂˣ)
    (T : Subgroup G) (hT : IsOpen (T : Set G)) (h : ContinuousOn χ (T : Set G)) : Continuous χ :=
  continuous_of_continuousAt_one χ (h.continuousAt (hT.mem_nhds T.one_mem))

end Join

section Lift
open Module

private theorem exists_exp_two_pi_I_mul_eq {z : ℂ} (hz : ‖z‖ = 1) : ∃ t : ℝ, exp (2 * Real.pi * I * t) = z := by
  refine ⟨arg z / (2 * Real.pi), ?_⟩
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2 : (2 * Real.pi * I : ℂ) * ((arg z / (2 * Real.pi) : ℝ) : ℂ) = arg z * I := by
    push_cast
    field_simp
  rw [h2]
  have h := norm_mul_exp_arg_mul_I z
  rwa [hz, ofReal_one, one_mul] at h

private theorem exists_int_of_exp_two_pi_I_mul_eq_one {t : ℝ} (ht : exp (2 * Real.pi * I * t) = 1) :
    ∃ n : ℤ, t = n := by
  obtain ⟨n, hn⟩ := exp_eq_one_iff.mp ht
  refine ⟨n, ?_⟩
  have h2 : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have h3 : (t : ℂ) = n := by
    have h4 : (2 * Real.pi * I : ℂ) * t = (2 * Real.pi * I) * n := by rw [hn]; ring
    exact mul_left_cancel₀ h2 h4
  exact_mod_cast h3

private theorem exists_linearMap_exp_eq_of_isZLattice {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [hdisc : DiscreteTopology L] [hlat : IsZLattice ℝ L]
    (f : L →+ Additive circleUnits) :
    ∃ ℓ : E →ₗ[ℝ] ℝ, ∀ g : L, exp (2 * Real.pi * I * ℓ g) = (((Additive.toMul (f g) : circleUnits) : ℂˣ) : ℂ) := by
  classical
  let b := Module.Free.chooseBasis ℤ L
  let bE := b.ofZLatticeBasis ℝ L
  have hval : ∀ j, ‖(((Additive.toMul (f (b j)) : circleUnits) : ℂˣ) : ℂ)‖ = 1 := fun j => (Additive.toMul (f (b j))).2
  choose t ht using fun j => exists_exp_two_pi_I_mul_eq (hval j)
  refine ⟨∑ j, t j • bE.coord j, fun g => ?_⟩
  have hrepr : (∑ j, t j • bE.coord j) (g : E) = ∑ j, (b.repr g j : ℝ) * t j := by
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Basis.coord_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Basis.ofZLatticeBasis_repr_apply ℝ L b g j, mul_comm]
  have hg : g = ∑ j, b.repr g j • b j := (b.sum_repr g).symm
  rw [hrepr]
  conv_rhs => rw [hg]
  rw [map_sum]
  simp only [map_zsmul, toMul_sum, toMul_zsmul]
  rw [Subgroup.val_finset_prod, Units.coe_prod]
  push_cast
  rw [Finset.mul_sum, exp_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← ht j, ← exp_int_mul]
  congr 1
  push_cast
  ring

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

private theorem exists_linearMap_exp_eq_of_discrete (Γ : Submodule ℤ V) [DiscreteTopology Γ]
    (f : Γ →+ Additive circleUnits) :
    ∃ ℓ : V →ₗ[ℝ] ℝ, ∀ g : Γ, exp (2 * Real.pi * I * ℓ g) = (((Additive.toMul (f g) : circleUnits) : ℂˣ) : ℂ) := by
  let W : Submodule ℝ V := Submodule.span ℝ (Γ : Set V)
  have hΓW : Γ ≤ W.restrictScalars ℤ := fun g hg => Submodule.subset_span hg
  let L : Submodule ℤ W := Submodule.comap (W.restrictScalars ℤ).subtype Γ
  let e : Γ ≃ₗ[ℤ] L := (Submodule.comapSubtypeEquivOfLe hΓW).symm
  have hdisc : DiscreteTopology L := by
    let e' : Γ ≃L[ℤ] L := ⟨e, continuous_of_discreteTopology, Isometry.continuous fun _ _ => rfl⟩
    exact e'.toHomeomorph.discreteTopology
  have hlat : @IsZLattice ℝ _ W _ _ L hdisc :=
    @IsZLattice.mk ℝ _ W _ _ L hdisc (by
      show Submodule.span ℝ (Subtype.val ⁻¹' (Γ : Set V) : Set W) = ⊤
      exact Submodule.span_span_coe_preimage)
  let f' : L →+ Additive circleUnits := f.comp e.symm.toLinearMap.toAddMonoidHom
  obtain ⟨ℓW, hℓW⟩ := exists_linearMap_exp_eq_of_isZLattice L (hdisc := hdisc) (hlat := hlat) f'
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective W.subtype (Submodule.ker_subtype W)
  have hπW : ∀ w : W, π w = w := fun w => LinearMap.congr_fun hπ w
  refine ⟨ℓW.comp π, fun g => ?_⟩
  have hπg : π g = ((e g : L) : W) := hπW ⟨g, hΓW g.2⟩
  rw [LinearMap.comp_apply, hπg, hℓW (e g)]
  simp [f']

end Lift

end IdeleClassSeparation
end TwistAbstract

section TwistAssembly
open NumberField IsDedekindDomain Complex

namespace IdeleClassSeparation

variable {F : Type} [Field F] [NumberField F]

private theorem eq_of_forall_archValue_principal_eq {u u' : Fˣ}
    (h : ∀ w : InfinitePlace F, archValue F w (principal F u) = archValue F w (principal F u')) : u = u' := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have hw := h w
  rw [archValue_principal, archValue_principal] at hw
  exact Units.ext (w.embedding.injective hw)

section Interpolation

variable (F)

private noncomputable abbrev unitsLattice : Submodule ℤ (ArchCoord F) := (archLattice F (unitBox F)).toIntSubmodule

variable {F}

private theorem mem_unitsLattice {v : ArchCoord F} : v ∈ unitsLattice F ↔ v ∈ archLattice F (unitBox F) := Iff.rfl

private noncomputable def unitOf (x : unitsLattice F) : Fˣ := Classical.choose ((mem_archLattice).1 x.2)

private theorem principal_unitOf_mem (x : unitsLattice F) : principal F (unitOf x) ∈ unitBox F :=
  (Classical.choose_spec ((mem_archLattice).1 x.2)).1

private theorem archExp_eq_archValue_principal_unitOf (x : unitsLattice F) (w : InfinitePlace F) :
    archExp F (x : ArchCoord F) w = archValue F w (principal F (unitOf x)) :=
  (Classical.choose_spec ((mem_archLattice).1 x.2)).2 w

private theorem unitOf_eq {x : unitsLattice F} {u : Fˣ}
    (h : ∀ w : InfinitePlace F, archExp F (x : ArchCoord F) w = archValue F w (principal F u)) : unitOf x = u :=
  eq_of_forall_archValue_principal_eq fun w => by rw [← archExp_eq_archValue_principal_unitOf, h w]

private theorem unitOf_add (x y : unitsLattice F) : unitOf (x + y) = unitOf x * unitOf y :=
  unitOf_eq fun w => by
    rw [Submodule.coe_add, archExp_add, archExp_eq_archValue_principal_unitOf x,
      archExp_eq_archValue_principal_unitOf y, map_mul, archValue_mul]

variable (φ : Fˣ →* ℂˣ) (hφ : ∀ u : Fˣ, principal F u ∈ unitBox F → ‖((φ u : ℂˣ) : ℂ)‖ = 1)
include hφ

private noncomputable def latticeChar : unitsLattice F →+ Additive circleUnits :=
  AddMonoidHom.mk' (fun x => Additive.ofMul (⟨φ (unitOf x), hφ _ (principal_unitOf_mem x)⟩ : circleUnits))
    (fun x y => by
      rw [← ofMul_mul]
      exact congrArg Additive.ofMul (Subtype.ext (by simp only [Subgroup.coe_mul, unitOf_add, map_mul])))

private theorem toMul_latticeChar (x : unitsLattice F) :
    (((Additive.toMul (latticeChar φ hφ x) : circleUnits) : ℂˣ) : ℂ) = ((φ (unitOf x) : ℂˣ) : ℂ) := rfl

private theorem exists_archChar_principal_eq :
    ∃ (c : InfinitePlace F → ℝ) (n : InfinitePlace F → ℤ), ∀ u : Fˣ, principal F u ∈ unitBox F →
      archChar F c n (principal F u) = φ u := by
  haveI : DiscreteTopology (archLattice F (unitBox F)) := discreteTopology_archLattice le_rfl
  haveI : DiscreteTopology (unitsLattice F) := inferInstanceAs (DiscreteTopology (archLattice F (unitBox F)))
  obtain ⟨ℓ, hℓ⟩ := exists_linearMap_exp_eq_of_discrete (unitsLattice F) (latticeChar φ hφ)
  have hper : ∀ w : InfinitePlace F, ∃ n : ℤ, ℓ (argPeriod F w) = n := by
    intro w
    set p : unitsLattice F := ⟨argPeriod F w, argPeriod_mem_archLattice (unitBox F) w⟩
    have hp : unitOf p = 1 := unitOf_eq fun w' => by
      simp only [p, archExp_argPeriod, map_one, archValue_one]
    have h := hℓ p
    rw [toMul_latticeChar, hp, map_one, Units.val_one] at h
    exact exists_int_of_exp_two_pi_I_mul_eq_one h
  obtain ⟨c, n, hcn⟩ := exists_archChar_eq_exp_linearMap ℓ hper
  refine ⟨c, n, fun u hu => ?_⟩
  set x : unitsLattice F := ⟨archCoord F (principal F u), archCoord_principal_mem_archLattice hu⟩
  have hx : unitOf x = u := unitOf_eq fun w => by simp only [x, archExp_archCoord]
  have h := hℓ x
  rw [toMul_latticeChar, hx] at h
  apply Units.ext
  rw [hcn]
  exact h

end Interpolation

section Assembly

variable (F)

private noncomputable def finUnit (v : HeightOneSpectrum (𝓞 F)) : (AdeleRing (𝓞 F) F)ˣ →* (v.adicCompletion F)ˣ where
  toFun x := Units.mk0 (finComp F x v) (finComp_ne_zero x v)
  map_one' := Units.ext (by simp [finComp_one])
  map_mul' x y := Units.ext (by simp [finComp_mul])

private theorem val_finUnit (v : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ) :
    ((finUnit F v x : (v.adicCompletion F)ˣ) : v.adicCompletion F) = finComp F x v := rfl

variable (S : Finset (HeightOneSpectrum (𝓞 F)))
  (eps : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ)

private noncomputable def sChar : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ := ∏ v ∈ S, (eps v).comp (finUnit F v)

private theorem sChar_apply (x : (AdeleRing (𝓞 F) F)ˣ) : sChar F S eps x = ∏ v ∈ S, eps v (finUnit F v x) := by
  simp only [sChar, MonoidHom.finset_prod_apply, MonoidHom.comp_apply]

variable {F S eps}

private theorem norm_sChar_apply
    (hunit : ∀ v ∈ S, ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 →
      ‖((eps v u : ℂˣ) : ℂ)‖ = 1)
    {x : (AdeleRing (𝓞 F) F)ˣ} (hx : x ∈ unitBox F) : ‖((sChar F S eps x : ℂˣ) : ℂ)‖ = 1 := by
  rw [sChar_apply, Units.coe_prod, norm_prod]
  exact Finset.prod_eq_one fun v hv => hunit v hv _ (by rw [val_finUnit]; exact valuation_finComp_eq_one hx v)

private theorem norm_archCharFn (c : InfinitePlace F → ℝ) (n : InfinitePlace F → ℤ) (y : (AdeleRing (𝓞 F) F)ˣ) :
    ‖archCharFn F c n y‖ = 1 := by
  unfold archCharFn
  rw [norm_prod]
  refine Finset.prod_eq_one fun w _ => ?_
  have h0 : ‖archValue F w y‖ ≠ 0 := (norm_archValue_pos w y).ne'
  rw [norm_mul, norm_zpow, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self h0, one_zpow,
    mul_one, Complex.norm_exp]
  simp

private theorem exists_twist_on_unitBox
    (hunit : ∀ v ∈ S, ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 →
      ‖((eps v u : ℂˣ) : ℂ)‖ = 1)
    (hcont : ∀ v ∈ S, ContinuousOn (fun x : (AdeleRing (𝓞 F) F)ˣ => eps v (finUnit F v x)) (unitBox F : Set _)) :
    ∃ μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ, (∀ u : Fˣ, μ (principal F u) = 1) ∧ Continuous μ ∧
      (∀ x, ‖((μ x : ℂˣ) : ℂ)‖ = 1) ∧ ∃ (c : InfinitePlace F → ℝ) (n : InfinitePlace F → ℤ),
        ∀ x ∈ unitBox F, μ x = archChar F c n x * (sChar F S eps x)⁻¹ := by

  obtain ⟨c, n, hcn⟩ := exists_archChar_principal_eq ((sChar F S eps).comp (principal F))
    (fun u hu => norm_sChar_apply hunit hu)
  let ψ₀ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ := archChar F c n * (sChar F S eps)⁻¹
  have hψ₀ : ∀ x, ψ₀ x = archChar F c n x * (sChar F S eps x)⁻¹ := fun x => rfl
  have hψ₀mem : ∀ s : unitBox F, ψ₀ s ∈ circleUnits := by
    intro s
    rw [mem_circleUnits, hψ₀, Units.val_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv,
      norm_sChar_apply hunit s.2, inv_one, mul_one, archChar_apply_val, norm_archCharFn]
  let ψ : unitBox F →* circleUnits := (ψ₀.comp (unitBox F).subtype).codRestrict circleUnits hψ₀mem
  have hψ : ∀ s : unitBox F, ((ψ s : circleUnits) : ℂˣ) = ψ₀ s := fun s => rfl
  have hψN : ∀ s : unitBox F, (s : (AdeleRing (𝓞 F) F)ˣ) ∈ (principal F).range → ψ s = 1 := by
    rintro ⟨s, hs⟩ ⟨u, rfl⟩
    apply Subtype.ext
    rw [hψ, hψ₀, hcn u hs, Subgroup.coe_one, MonoidHom.comp_apply, mul_inv_cancel]
  obtain ⟨χ, hχS, hχN⟩ :=
    exists_eq_on_of_eq_one_on_inf circleUnits_divisible (unitBox F) (principal F).range ψ hψN
  refine ⟨circleUnits.subtype.comp χ, fun u => ?_, ?_, fun x => (χ x).2, c, n, fun x hx => ?_⟩
  · rw [MonoidHom.comp_apply, hχN _ ⟨u, rfl⟩, map_one]
  · refine continuous_of_continuousOn_openSubgroup _ (unitBox F) (isOpen_unitBox F) ?_
    have hψ₀c : ContinuousOn ψ₀ (unitBox F : Set _) := by
      have h1 : ContinuousOn (fun x => archChar F c n x) (unitBox F : Set _) := (continuous_archChar c n).continuousOn
      have h2 : ContinuousOn (fun x => sChar F S eps x) (unitBox F : Set _) := by
        simp only [sChar_apply]
        exact continuousOn_finset_prod S fun v hv => hcont v hv
      exact h1.mul h2.inv
    refine hψ₀c.congr fun x hx => ?_
    have h := hχS ⟨x, hx⟩
    show ((χ x : circleUnits) : ℂˣ) = ψ₀ x
    rw [h, hψ]
  · have h := hχS ⟨x, hx⟩
    show ((χ x : circleUnits) : ℂˣ) = _
    rw [h, hψ, hψ₀]

private theorem twist_local_clause (c : InfinitePlace F → ℝ) (n : InfinitePlace F → ℤ) {μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    (hμ : ∀ x ∈ unitBox F, μ x = archChar F c n x * (sChar F S eps x)⁻¹)
    (ι : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* (AdeleRing (𝓞 F) F)ˣ)
    (hιSelf : ∀ (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ), finComp F (ι v u) v = u)
    (hιNe : ∀ (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ) (w : HeightOneSpectrum (𝓞 F)), w ≠ v →
      finComp F (ι v u) w = 1)
    (hιArch : ∀ (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ),
      ((ι v u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) (u : (v.adicCompletion F)ˣ)
    (hu : Valued.v (u : v.adicCompletion F) = 1) : μ (ι v u) * eps v u = 1 := by
  classical
  have hmem : ι v u ∈ unitBox F := by
    rw [mem_unitBox]
    intro w
    rw [← map_inv]
    by_cases hw : w = v
    · subst hw
      rw [hιSelf, hιSelf]
      refine ⟨?_, ?_⟩
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hu]
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
    · rw [hιNe v u w hw, hιNe v u⁻¹ w hw]
      exact ⟨one_mem _, one_mem _⟩
  have harch : archChar F c n (ι v u) = 1 := archChar_eq_one_of_fst_eq_one c n (hιArch v u)
  have hself : finUnit F v (ι v u) = u := Units.ext (by rw [val_finUnit, hιSelf])
  have hne : ∀ w, w ≠ v → finUnit F w (ι v u) = 1 := fun w hw => Units.ext (by rw [val_finUnit, hιNe v u w hw]; rfl)
  have hS : sChar F S eps (ι v u) = eps v u := by
    rw [sChar_apply, Finset.prod_eq_single v (fun w _ hwv => by rw [hne w hwv, map_one]) (fun h => absurd hv h),
      hself]
  rw [hμ _ hmem, harch, hS, one_mul, inv_mul_cancel]

private theorem twist_unramified_clause (c : InfinitePlace F → ℝ) (n : InfinitePlace F → ℤ)
    {μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    (hμ : ∀ x ∈ unitBox F, μ x = archChar F c n x * (sChar F S eps x)⁻¹)
    (ι : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* (AdeleRing (𝓞 F) F)ˣ)
    (hιSelf : ∀ (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ), finComp F (ι v u) v = u)
    (hιNe : ∀ (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ) (w : HeightOneSpectrum (𝓞 F)), w ≠ v →
      finComp F (ι v u) w = 1)
    (hιArch : ∀ (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ),
      ((ι v u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) (t : (v.adicCompletion F)ˣ)
    (ht : (t : v.adicCompletion F) ∈ v.adicCompletionIntegers F)
    (ht' : ((t⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F) :
    μ (ι v t) = 1 := by
  classical
  have hmem : ι v t ∈ unitBox F := by
    rw [mem_unitBox]
    intro w
    rw [← map_inv]
    by_cases hw : w = v
    · subst hw
      rw [hιSelf, hιSelf]
      exact ⟨ht, ht'⟩
    · rw [hιNe v t w hw, hιNe v t⁻¹ w hw]
      exact ⟨one_mem _, one_mem _⟩
  have harch : archChar F c n (ι v t) = 1 := archChar_eq_one_of_fst_eq_one c n (hιArch v t)
  have hne : ∀ w, w ≠ v → finUnit F w (ι v t) = 1 := fun w hw => Units.ext (by rw [val_finUnit, hιNe v t w hw]; rfl)
  have hS : sChar F S eps (ι v t) = 1 := by
    rw [sChar_apply]
    exact Finset.prod_eq_one fun w hw => by rw [hne w (fun h => hv (h ▸ hw)), map_one]
  rw [hμ _ hmem, harch, hS, inv_one, mul_one]

end Assembly

end IdeleClassSeparation
end TwistAssembly

namespace IdeleClassSeparation

private theorem norm_eq_one_of_forall_zpow_norm_le (z : ℂˣ) (B : ℝ)
    (hB : ∀ n : ℤ, ‖((z ^ n : ℂˣ) : ℂ)‖ ≤ B) : ‖(z : ℂ)‖ = 1 := by
  have hpos : 0 < ‖(z : ℂ)‖ := norm_pos_iff.2 z.ne_zero
  rcases lt_trichotomy ‖(z : ℂ)‖ 1 with h | h | h
  · exfalso
    have h1 : 1 < ‖(z : ℂ)‖⁻¹ := (one_lt_inv₀ hpos).2 h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B h1
    have hn' := hB (-(n : ℤ))
    rw [zpow_neg, zpow_natCast, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, norm_inv, norm_pow,
      ← inv_pow] at hn'
    exact absurd hn' (not_le.2 hn)
  · exact h
  · exfalso
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B h
    have hn' := hB n
    rw [zpow_natCast, Units.val_pow_eq_pow_val, norm_pow] at hn'
    exact absurd hn' (not_le.2 hn)

private theorem exists_forall_norm_le_of_continuousOn {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsCompact s) (f : X → ℂ) (hf : ContinuousOn f s) : ∃ B : ℝ, ∀ x ∈ s, ‖f x‖ ≤ B := by
  obtain ⟨B, hB⟩ := (hs.image_of_continuousOn hf).isBounded.exists_norm_le
  exact ⟨B, fun x hx => hB _ ⟨x, hx, rfl⟩⟩

private theorem norm_eq_one_of_continuousOn_of_zpow_mem {G : Type*} [Group G] [TopologicalSpace G] {s : Set G}
    (hs : IsCompact s) (φ : G →* ℂˣ) (hφ : ContinuousOn (fun g => ((φ g : ℂˣ) : ℂ)) s) (u : G)
    (hu : ∀ n : ℤ, u ^ n ∈ s) : ‖((φ u : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨B, hB⟩ := exists_forall_norm_le_of_continuousOn hs _ hφ
  refine norm_eq_one_of_forall_zpow_norm_le (φ u) B fun n => ?_
  rw [← map_zpow]
  exact hB _ (hu n)

end IdeleClassSeparation

section LevelDischarge

open IsDedekindDomain NumberField Filter Topology

variable {F : Type} [Field F] [NumberField F]

open LanglandsTunnell.Converse (IsOneMod)

namespace IdeleClassSeparation

variable {v : HeightOneSpectrum (𝓞 F)}

private theorem ball_lt_mem_nhds (y t : v.adicCompletion F) (ht : t ≠ 0) :
    {z : v.adicCompletion F | Valued.v (z - y) < Valued.v t} ∈ 𝓝 y := by
  have hball : IsOpen {z : v.adicCompletion F | Valued.v (z - y) < Valued.v t} := by
    have h := (Valued.isOpen_ball (R := v.adicCompletion F) (Valued.v.restrict t)).preimage (continuous_sub_right y)
    convert h using 1
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Valuation.restrict_lt_iff]
  refine hball.mem_nhds ?_
  simp only [Set.mem_setOf_eq, sub_self, map_zero]
  exact (Valuation.pos_iff _).mpr ht

variable {n : ℕ} {χ : (v.adicCompletion F)ˣ →* ℂˣ}
  (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → IsOneMod F v n u → χ u = 1)
include hχ

private theorem level_eq_of_sub_lt {z z₀ : v.adicCompletion F} (hz₀ : z₀ ≠ 0)
    (h : Valued.v (z - z₀) < WithZero.exp (-(n : ℤ)) * Valued.v z₀) (hz : z ≠ 0) :
    χ (Units.mk0 z hz) = χ (Units.mk0 z₀ hz₀) := by
  have hexp : WithZero.exp (-(n : ℤ)) ≤ (1 : WithZero (Multiplicative ℤ)) := by
    rw [← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (by omega)
  have hlt : Valued.v (z - z₀) < Valued.v z₀ :=
    lt_of_lt_of_le h (by simpa using mul_le_mul_left hexp (Valued.v z₀))
  have hval : Valued.v z = Valued.v z₀ := Valuation.map_eq_of_sub_lt _ hlt
  have hz₀v : Valued.v z₀ ≠ 0 := (Valuation.ne_zero_iff _).mpr hz₀
  set w : (v.adicCompletion F)ˣ := Units.mk0 z hz * (Units.mk0 z₀ hz₀)⁻¹ with hw
  have hw1 : Valued.v (w : v.adicCompletion F) = 1 := by
    rw [hw, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0, map_mul, map_inv₀, hval]
    exact mul_inv_cancel₀ hz₀v
  have hwmod : IsOneMod F v n w := by
    unfold IsOneMod
    have hw' : (w : v.adicCompletion F) - 1 = (z - z₀) * z₀⁻¹ := by
      rw [hw, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0, sub_mul,
        mul_inv_cancel₀ hz₀]
    rw [hw', map_mul, map_inv₀]
    calc Valued.v (z - z₀) * (Valued.v z₀)⁻¹
        ≤ WithZero.exp (-(n : ℤ)) * Valued.v z₀ * (Valued.v z₀)⁻¹ := mul_le_mul_left h.le _
      _ = WithZero.exp (-(n : ℤ)) := mul_inv_cancel_right₀ hz₀v _
  have hχw : χ w = 1 := hχ w hw1 hwmod
  have hzw : Units.mk0 z hz = w * Units.mk0 z₀ hz₀ := by rw [hw, inv_mul_cancel_right]
  rw [hzw, map_mul, hχw, one_mul]

private theorem eventually_eq_of_level {z₀ : v.adicCompletion F} (hz₀ : z₀ ≠ 0) :
    ∀ᶠ z in 𝓝 z₀, ∀ hz : z ≠ 0, χ (Units.mk0 z hz) = χ (Units.mk0 z₀ hz₀) := by
  have hz₀v : Valued.v z₀ ≠ 0 := (Valuation.ne_zero_iff _).mpr hz₀
  obtain ⟨t, ht⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (-(n : ℤ)) * Valued.v z₀)
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, map_zero] at ht
    exact mul_ne_zero WithZero.exp_ne_zero hz₀v ht.symm
  filter_upwards [ball_lt_mem_nhds z₀ t ht0] with z hz hzne
  exact level_eq_of_sub_lt hχ hz₀ (lt_of_lt_of_eq hz ht) hzne

private theorem norm_eq_one_of_level [CompactSpace (v.adicCompletionIntegers F)] (u : (v.adicCompletion F)ˣ)
    (hu : Valued.v (u : v.adicCompletion F) = 1) : ‖((χ u : ℂˣ) : ℂ)‖ = 1 := by
  have hO : IsCompact ((v.adicCompletionIntegers F).toSubring.toSubmonoid : Set (v.adicCompletion F)) :=
    isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace (v.adicCompletionIntegers F)))
  have hs : IsCompact (((v.adicCompletionIntegers F).toSubring.toSubmonoid.units : Subgroup _) :
      Set (v.adicCompletion F)ˣ) :=
    Submonoid.units_isCompact hO
  have hu' : Valued.v ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
  have humem : u ∈ (v.adicCompletionIntegers F).toSubring.toSubmonoid.units :=
    ⟨(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hu.le,
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hu'.le⟩
  have hcont : ContinuousOn (fun w : (v.adicCompletion F)ˣ => ((χ w : ℂˣ) : ℂ))
      (((v.adicCompletionIntegers F).toSubring.toSubmonoid.units : Subgroup _) : Set (v.adicCompletion F)ˣ) := by
    intro w₀ _
    refine ContinuousAt.continuousWithinAt ?_
    have h2 : Units.val ⁻¹' {z : v.adicCompletion F | ∀ hz : z ≠ 0,
        χ (Units.mk0 z hz) = χ (Units.mk0 (w₀ : v.adicCompletion F) w₀.ne_zero)} ∈ 𝓝 w₀ :=
      Units.continuous_val.continuousAt.preimage_mem_nhds (eventually_eq_of_level hχ w₀.ne_zero)
    refine (continuousAt_const : ContinuousAt (fun _ => ((χ w₀ : ℂˣ) : ℂ)) w₀).congr ?_
    filter_upwards [h2] with w hw
    have hw' := hw w.ne_zero
    rw [Units.mk0_val, Units.mk0_val] at hw'
    show ((χ w₀ : ℂˣ) : ℂ) = ((χ w : ℂˣ) : ℂ)
    rw [hw']
  exact norm_eq_one_of_continuousOn_of_zpow_mem hs χ hcont u fun k => zpow_mem humem k

private theorem continuous_level_comp_finUnit : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => χ (finUnit F v x) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  have h2 : (fun x : (AdeleRing (𝓞 F) F)ˣ => finComp F x v) ⁻¹' {z : v.adicCompletion F | ∀ hz : z ≠ 0,
      χ (Units.mk0 z hz) = χ (Units.mk0 (finComp F x₀ v) (finComp_ne_zero x₀ v))} ∈ 𝓝 x₀ :=
    (continuous_finComp v).continuousAt.preimage_mem_nhds (eventually_eq_of_level hχ (finComp_ne_zero x₀ v))
  refine (continuousAt_const : ContinuousAt (fun _ => χ (finUnit F v x₀)) x₀).congr ?_
  filter_upwards [h2] with x hx
  exact (hx (finComp_ne_zero x v)).symm

end IdeleClassSeparation

end LevelDischarge

open IsDedekindDomain NumberField LanglandsTunnell.Converse IdeleClassSeparation

theorem solution (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ) (m : ↥S → ℕ)
    (hlevel : ∀ (v : ↥S) (u : (v.1.adicCompletion K)ˣ), Valued.v (u : v.1.adicCompletion K) = 1 →
      IsOneMod K v.1 (m v) u → epsS v.1 u = 1) :
    ∃ μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, IsJLTwist K S epsS μ ∧
      ∀ v ∉ S, NumberField.TateGlobal.IsUnramifiedCharAt μ v := by
  have hunit : ∀ v ∈ S, ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 →
      ‖((epsS v u : ℂˣ) : ℂ)‖ = 1 :=
    fun v hv u hu => norm_eq_one_of_level (fun u hu hmod => hlevel ⟨v, hv⟩ u hu hmod) u hu
  have hcont : ∀ v ∈ S, ContinuousOn (fun x : (AdeleRing (𝓞 K) K)ˣ => epsS v (finUnit K v x)) (unitBox K : Set _) :=
    fun v hv => (continuous_level_comp_finUnit (fun u hu hmod => hlevel ⟨v, hv⟩ u hu hmod)).continuousOn
  obtain ⟨μ, hprin, hμc, hμu, c, n, hμ⟩ := exists_twist_on_unitBox hunit hcont
  let ι : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* (AdeleRing (𝓞 K) K)ˣ := fun v =>
    (Units.map (NumberField.AdelicLevel.finIncl (𝓞 K) K)).comp (NumberField.AdelicLevel.localUnit (𝓞 K) K v)
  have hιSelf : ∀ (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ), finComp K (ι v u) v = u :=
    fun v u => NumberField.AdelicLevel.localUnit_apply_self (𝓞 K) K v u
  have hιNe : ∀ (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ) (w : HeightOneSpectrum (𝓞 K)), w ≠ v →
      finComp K (ι v u) w = 1 :=
    fun v u w hw => NumberField.AdelicLevel.localUnit_apply_of_ne (𝓞 K) K v u hw
  have hιArch : ∀ (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ),
      ((ι v u : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = 1 :=
    fun v u => rfl
  refine ⟨μ, ⟨⟨fun u => hprin u, hμc, hμu⟩, fun v hv u hu => ?_⟩, fun v hv t ht ht' => ?_⟩
  · exact twist_local_clause c n hμ ι hιSelf hιNe hιArch hv u hu
  · exact twist_unramified_clause c n hμ ι hιSelf hιNe hιArch hv t ht ht'

end S_LanglandsTunnell_Converse_exists_isJLTwist
end P2MW
export P2MW.S_LanglandsTunnell_Converse_exists_isJLTwist (solution)
