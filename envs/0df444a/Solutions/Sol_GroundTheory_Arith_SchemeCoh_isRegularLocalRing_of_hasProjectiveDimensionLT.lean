-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.isRegularLocalRing_of_hasProjectiveDimensionLT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:54:31.687585+00:00
-- url     : https://prove2.me/submissions/70a8664b-6fd6-44a5-8d89-62cfeda0483f

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDSerre
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDLocalization
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_hasProjectiveDimensionLT_quotSMulTop
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_eq_zero_of_forall_smul_eq_zero_of_free
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_free_of_hasProjectiveDimensionLT_of_mul_eq_zero
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_spanFinrank_maximalIdeal_le_quotient_add_one
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_spanFinrank_maximalIdeal_quotient_add_one_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open IsLocalRing Ideal CategoryTheory Abelian
open scoped Pointwise
universe u
variable {R : Type u} [CommRing R]
set_option backward.isDefEq.respectTransparency false
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution [IsLocalRing R] [IsNoetherianRing R]
    (n : ℕ) (hk : HasProjectiveDimensionLT (ModuleCat.of R (R ⧸ maximalIdeal R)) (n + 1)) :
    IsRegularLocalRing R := by
  suffices H : ∀ e : ℕ, ∀ (S : Type u) [CommRing S] [IsLocalRing S] [IsNoetherianRing S] (n : ℕ),
      HasProjectiveDimensionLT (ModuleCat.of S (S ⧸ maximalIdeal S)) (n + 1) →
      (maximalIdeal S).spanFinrank = e → IsRegularLocalRing S from H _ R n hk rfl
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
  intro S _ _ _ n hk he
  have hfg : (maximalIdeal S).FG := (maximalIdeal S).fg_of_isNoetherianRing
  by_cases he0 : e = 0
  · apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    rw [he, he0]
    exact_mod_cast ringKrullDim_nonneg_of_nontrivial
  have hjac : maximalIdeal S ≤ jacobson ⊥ :=
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  have hmne : maximalIdeal S ≠ ⊥ := fun h ↦ he0 (by rw [← he, h]; simp)
  by_cases hass : maximalIdeal S ∈ associatedPrimes S S
  ·
    exfalso
    obtain ⟨-, s, hs⟩ := (isAssociatedPrime_iff (I := maximalIdeal S) (M := S)).mp hass
    have hms : ∀ a ∈ maximalIdeal S, a * s = 0 := fun a ha ↦ by
      have := hs ▸ ha
      simpa [Submodule.mem_colon_singleton, smul_eq_mul] using this
    have hs0 : s ≠ 0 := by
      rintro rfl
      have h1 : (1 : S) ∈ maximalIdeal S := by
        rw [hs]; simp [Submodule.mem_colon_singleton]
      exact (IsLocalRing.maximalIdeal.isMaximal S).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    have hfree := free_of_hasProjectiveDimensionLT_of_mul_eq_zero hs0 hms n
      (S ⧸ maximalIdeal S) hk
    apply hmne
    rw [eq_bot_iff]
    intro a ha
    rw [Submodule.mem_bot]
    exact eq_zero_of_forall_smul_eq_zero_of_free (M := S ⧸ maximalIdeal S) fun y ↦ by
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
        Ideal.Quotient.eq_zero_iff_mem]
      exact (maximalIdeal S).mul_mem_right y ha

  have hsq : ¬ maximalIdeal S ≤ maximalIdeal S ^ 2 := by
    intro hle
    exact hmne (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hfg
      (by simpa [pow_two, smul_eq_mul] using hle) hjac)
  classical
  have hfin := associatedPrimes.finite S S
  obtain ⟨x, hx, hxn⟩ : ∃ x ∈ maximalIdeal S,
      x ∉ ⋃ i ∈ (↑(insert (maximalIdeal S ^ 2) hfin.toFinset) : Set (Ideal S)), (i : Set S) := by
    by_contra! hcon
    obtain ⟨i, hi, hle⟩ := (Ideal.subset_union_prime (f := id) (maximalIdeal S ^ 2)
      (maximalIdeal S ^ 2) (fun i hi h1 _ ↦ by
        rcases Finset.mem_insert.mp hi with h | h
        · exact absurd h h1
        · exact ((Set.Finite.mem_toFinset _).mp h).isPrime)).mp hcon
    rcases Finset.mem_insert.mp hi with h | h
    · exact hsq (h ▸ hle)
    · have hP := (Set.Finite.mem_toFinset _).mp h
      have : i = maximalIdeal S :=
        le_antisymm (IsLocalRing.le_maximalIdeal hP.isPrime.ne_top) hle
      exact hass (this ▸ hP)
  simp only [Finset.coe_insert, Set.Finite.coe_toFinset, Set.mem_insert_iff,
    Set.iUnion_iUnion_eq_or_left, Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hxn
  obtain ⟨hx2, hxP⟩ := hxn
  have hxreg : IsSMulRegular S x := by
    have : x ∉ ⋃ p ∈ associatedPrimes S S, (p : Set S) := by
      simp only [Set.mem_iUnion, not_exists]
      exact fun p hp hxp ↦ hxP p hp hxp
    rw [biUnion_associatedPrimes_eq_compl_regular S S] at this
    simpa using this

  have hne : span {x} ≠ ⊤ := fun h ↦ (IsLocalRing.maximalIdeal.isMaximal S).ne_top
    (top_le_iff.mp (h ▸ (span_singleton_le_iff_mem _).mpr hx))
  have : Nontrivial (S ⧸ span {x}) := Ideal.Quotient.nontrivial_iff.mpr hne
  have : IsLocalRing (S ⧸ span {x}) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have hloc : IsLocalHom (Ideal.Quotient.mk (span {x})) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective

  let T := ModuleCat.shortComplexOfCompEqZero (maximalIdeal S).subtype (maximalIdeal S).mkQ
    (LinearMap.exact_subtype_mkQ _).linearMap_comp_eq_zero
  have hT : T.ShortExact := ModuleCat.shortComplex_shortExact T
    (LinearMap.exact_subtype_mkQ _) (Submodule.injective_subtype _) (Submodule.mkQ_surjective _)
  have : HasProjectiveDimensionLT T.X₃ (n + 1) := hk
  have hk2 : HasProjectiveDimensionLT T.X₃ (n + 2) :=
    hasProjectiveDimensionLT_of_ge T.X₃ (n + 1) (n + 2) (by omega)
  have hproj : Projective T.X₂ := by
    rw [← IsProjective.iff_projective]; infer_instance
  have hm : HasProjectiveDimensionLT (ModuleCat.of S (maximalIdeal S)) (n + 1) :=
    (hT.hasProjectiveDimensionLT_X₃_iff n hproj).mp hk2
  have hxm : IsSMulRegular (maximalIdeal S) x :=
    fun a b h ↦ Subtype.ext (hxreg (congrArg Subtype.val h))
  have hB := hasProjectiveDimensionLT_quotSMulTop hxreg n (maximalIdeal S) hxm hm

  let x' : maximalIdeal S := ⟨x, hx⟩
  let ι₀ : (S ⧸ span {x}) →ₗ[S ⧸ span {x}] QuotSMulTop x (maximalIdeal S) :=
    LinearMap.toSpanSingleton (S ⧸ span {x}) _ (Submodule.mkQ _ x')
  have hι : maximalIdeal (S ⧸ span {x}) ≤ LinearMap.ker ι₀ := by
    intro b hb
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    have ha : a ∈ maximalIdeal S := by
      rw [← IsLocalRing.maximalIdeal_comap (Ideal.Quotient.mk (span {x}))]; exact hb
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply,
      show Ideal.Quotient.mk (span {x}) a = algebraMap S (S ⧸ span {x}) a from rfl,
      algebraMap_smul, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨⟨a, ha⟩, Submodule.mem_top, Subtype.ext (mul_comm x a)⟩
  let ι := (maximalIdeal (S ⧸ span {x})).liftQ ι₀ hι
  let v0 := (maximalIdeal S).toCotangent x'
  have hv0 : v0 ≠ 0 := by
    rw [Ne, Ideal.toCotangent_eq_zero]
    simpa [pow_two] using hx2
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one (ResidueField S) hv0
  let q : (S ⧸ maximalIdeal S) →ₐ[S] (S ⧸ span {x}) ⧸ maximalIdeal (S ⧸ span {x}) :=
    Ideal.quotientMapₐ (maximalIdeal (S ⧸ span {x})) (Ideal.Quotient.mkₐ S (span {x})) (by
      intro a ha
      rw [Ideal.mem_comap, Ideal.Quotient.mkₐ_eq_mk, ← Ideal.mem_comap,
        IsLocalRing.maximalIdeal_comap]
      exact ha)
  let φ : maximalIdeal S →ₗ[S] (S ⧸ span {x}) ⧸ maximalIdeal (S ⧸ span {x}) :=
    q.toLinearMap ∘ₗ (f.restrictScalars S) ∘ₗ (maximalIdeal S).toCotangent
  have hxq : algebraMap S ((S ⧸ span {x}) ⧸ maximalIdeal (S ⧸ span {x})) x = 0 := by
    rw [IsScalarTower.algebraMap_apply S (S ⧸ span {x}),
      show algebraMap S (S ⧸ span {x}) x = 0 from
        Ideal.Quotient.eq_zero_iff_mem.mpr (mem_span_singleton_self x), map_zero]
  have hφ : x • (⊤ : Submodule S (maximalIdeal S)) ≤ LinearMap.ker φ := by
    intro y hy
    obtain ⟨z, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy
    rw [LinearMap.mem_ker, map_smul, Algebra.smul_def, hxq, zero_mul]
  let ρ₀ : QuotSMulTop x (maximalIdeal S) →ₗ[S] (S ⧸ span {x}) ⧸ maximalIdeal (S ⧸ span {x}) :=
    (x • (⊤ : Submodule S (maximalIdeal S))).liftQ φ hφ
  let ρ := ρ₀.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective (I := span {x}))
  have hρι : ρ ∘ₗ ι = LinearMap.id := by
    apply Submodule.linearMap_qext
    apply LinearMap.ext_ring
    have h1 : f v0 = 1 := hf
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, ι, Submodule.liftQ_apply, ι₀,
      LinearMap.toSpanSingleton_apply, one_smul, ρ, LinearMap.extendScalarsOfSurjective_apply,
      ρ₀, φ, LinearMap.coe_comp, Function.comp_apply, LinearMap.id_apply]
    change q (f v0) = _
    rw [h1, map_one]
    rfl
  let rt : Retract (ModuleCat.of (S ⧸ span {x}) ((S ⧸ span {x}) ⧸ maximalIdeal (S ⧸ span {x})))
      (ModuleCat.of (S ⧸ span {x}) (QuotSMulTop x (maximalIdeal S))) :=
    { i := ModuleCat.ofHom ι
      r := ModuleCat.ofHom ρ
      retract := by rw [← ModuleCat.ofHom_comp, hρι, ModuleCat.ofHom_id] }
  have hkB := rt.hasProjectiveDimensionLT (n + 1)
  have hlt := spanFinrank_maximalIdeal_quotient_add_one_le hx hx2
  have hregB := ih _ (by omega) (S ⧸ span {x}) n hkB rfl
  have hdimB := (isRegularLocalRing_iff (S ⧸ span {x})).mp hregB
  have hdim : ringKrullDim (S ⧸ span {x}) + 1 = ringKrullDim S :=
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hxreg hx
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  have h1 := spanFinrank_maximalIdeal_le_quotient_add_one (R := S) (x := x)
  rw [← hdim, ← hdimB]
  exact_mod_cast h1
end GroundTheory.Arith.SchemeCoh
