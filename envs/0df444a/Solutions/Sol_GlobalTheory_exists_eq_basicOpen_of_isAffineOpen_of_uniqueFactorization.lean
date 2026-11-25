-- Prove2me | solution 1 for GlobalTheory.exists_eq_basicOpen_of_isAffineOpen_of_uniqueFactorization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:49:16.195364+00:00
-- url     : https://prove2.me/submissions/f241a8a3-36fe-4c19-a8ec-05e62c1e6460

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__DimEqZero_40b4adf5f58b53e3
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsPowMulMemRangeOfLocalDenominators
import Theorems.Thm_GlobalTheory_exists_pow_mul_mem_range_of_local_denominators
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_GrSum_map_of
import Theorems.Thm_GlobalTheory_IsGradedMap_comp
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
import Theorems.Thm_GlobalTheory_locCubeMap_id
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.GrSum.map_of
attribute [local simp] GlobalTheory.Wick.dividedContraction_one
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [UniqueFactorizationMonoid A] (U : (Spec (CommRingCat.of A)).Opens), IsAffineOpen U → (U : Set (Spec (CommRingCat.of A))).Nonempty → ∃ a : A, U = PrimeSpectrum.basicOpen a := by
  classical
  intro A _ _ _ _ U hU hne
  have hloc : ∀ p : PrimeSpectrum A, p ∈ U → ∃ f : A,
      p ∈ PrimeSpectrum.basicOpen f ∧ PrimeSpectrum.basicOpen f ≤ U := by
    intro p hp
    obtain ⟨_, ⟨f, rfl⟩, h1, h2⟩ :=
      (PrimeSpectrum.isTopologicalBasis_basic_opens (R := A)).exists_subset_of_mem_open hp U.isOpen
    exact ⟨f, h1, h2⟩
  obtain ⟨p₀, hp₀⟩ := hne
  obtain ⟨f, hf, hfU⟩ := hloc p₀ hp₀
  have hf0 : f ≠ 0 := fun h => hf (h ▸ p₀.asIdeal.zero_mem)
  let a : A := ((UniqueFactorizationMonoid.factors f).filter fun q =>
    ∃ p : PrimeSpectrum A, p.asIdeal = Ideal.span {q} ∧ p ∉ U).prod
  have ha : ∀ (q : A) (p : PrimeSpectrum A), Prime q → p.asIdeal = Ideal.span {q} →
      p ∉ U → q ∣ a := by
    intro q p hq hp hpU
    have hqf : q ∣ f := by
      rw [← Ideal.mem_span_singleton, ← hp]
      by_contra h
      exact hpU (hfU h)
    obtain ⟨r, hr, hqr⟩ :=
      UniqueFactorizationMonoid.exists_mem_factors_of_dvd hf0 hq.irreducible hqf
    refine hqr.dvd.trans (Multiset.dvd_prod (Multiset.mem_filter.2 ⟨hr, p, ?_, hpU⟩))
    rw [hp]
    exact Ideal.span_singleton_eq_span_singleton.2 hqr
  refine ⟨a, le_antisymm ?_ ?_⟩
  · intro p hp hpa
    have := p.isPrime
    obtain ⟨q, hq, hqp⟩ := (Ideal.IsPrime.multiset_prod_mem_iff_exists_mem p.isPrime _).1 hpa
    obtain ⟨-, p', hp', hp'U⟩ := Multiset.mem_filter.1 hq
    obtain ⟨g, hg, hgU⟩ := hloc p hp
    refine hp'U (hgU fun h => hg ?_)
    have h' : g ∈ p'.asIdeal := h
    rw [hp'] at h'
    exact (Ideal.span_singleton_le_iff_mem _).2 hqp h'
  · have : Nonempty U := ⟨⟨_, hp₀⟩⟩
    have hinj := map_injective_of_isIntegral (Spec (CommRingCat.of A)) (homOfLE (le_top : U ≤ ⊤))
    let φ : CommRingCat.of A ⟶ Γ(Spec (CommRingCat.of A), U) :=
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (Spec (CommRingCat.of A)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
    have hφ : Function.Injective φ :=
      hinj.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).1
    have key : ∀ (v : Γ(Spec (CommRingCat.of A), U)) (p : PrimeSpectrum A), p ∈ U →
        ∃ s, s ∉ p.asIdeal ∧ ∃ a, φ a = φ s * v := by
      intro v p hp
      let x : Spec (CommRingCat.of A) := p
      obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.surj (S := (Spec.structureSheaf A).presheaf.stalk p)
        p.asIdeal.primeCompl ((Spec (CommRingCat.of A)).presheaf.germ U x hp v)
      refine ⟨s, s.2, a, germ_injective_of_isIntegral _ x hp ?_⟩
      have hg : ∀ a : A, (Spec (CommRingCat.of A)).presheaf.germ U x hp (φ a) =
          algebraMap A ((Spec.structureSheaf A).presheaf.stalk p) a := by
        intro a
        exact ((Spec (CommRingCat.of A)).presheaf.germ_res_apply (homOfLE (le_top : U ≤ ⊤)) x hp
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)).trans rfl
      rw [map_mul, hg, hg]
      exact e.symm.trans (mul_comm _ _)
    have key2 : ∀ v : Γ(Spec (CommRingCat.of A), U), ∃ (n : ℕ) (x : A), φ x = φ a ^ n * v :=
      fun v => exists_pow_mul_mem_range_of_local_denominators φ.hom hφ
        (U : Set (Spec (CommRingCat.of A))) ⟨p₀, hp₀⟩ a ha v (key v)
    intro p hpa
    by_contra hpU
    have hspan : Ideal.span (φ '' {g : A | PrimeSpectrum.basicOpen g ≤ U}) = ⊤ := by
      rw [← hU.self_le_iSup_basicOpen_iff]
      intro x hx
      obtain ⟨g, hg, hgU⟩ := hloc x hx
      refine TopologicalSpace.Opens.mem_iSup.2 ⟨⟨φ g, g, hgU, rfl⟩, ?_⟩
      have e : (Spec (CommRingCat.of A)).basicOpen (φ g) = U ⊓ PrimeSpectrum.basicOpen g := by
        rw [← basicOpen_eq_of_affine (R := CommRingCat.of A) g]
        exact Scheme.basicOpen_res _ _ (homOfLE (le_top : U ≤ ⊤)).op
      show x ∈ (Spec (CommRingCat.of A)).basicOpen (φ g)
      rw [e]
      exact ⟨hx, hg⟩
    have hall : ∀ v ∈ Ideal.span (φ '' {g : A | PrimeSpectrum.basicOpen g ≤ U}),
        ∃ (n : ℕ) (x : A), x ∈ p.asIdeal ∧ φ x = φ a ^ n * v := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨g, hg, rfl⟩ := hv
        refine ⟨0, g, ?_, by simp⟩
        by_contra h
        exact hpU (hg h)
      | zero => exact ⟨0, 0, p.asIdeal.zero_mem, by simp⟩
      | add v w _ _ hv hw =>
        obtain ⟨n, x, hx, e⟩ := hv
        obtain ⟨m, y, hy, e'⟩ := hw
        refine ⟨n + m, a ^ m * x + a ^ n * y,
          p.asIdeal.add_mem (p.asIdeal.mul_mem_left _ hx) (p.asIdeal.mul_mem_left _ hy), ?_⟩
        rw [map_add, map_mul, map_mul, map_pow, map_pow, e, e']
        ring
      | smul c v _ hv =>
        obtain ⟨n, x, hx, e⟩ := hv
        obtain ⟨m, y, e'⟩ := key2 c
        refine ⟨n + m, y * x, p.asIdeal.mul_mem_left _ hx, ?_⟩
        rw [map_mul, e, e', smul_eq_mul]
        ring
    obtain ⟨n, x, hx, e⟩ := hall 1 (hspan ▸ Submodule.mem_top)
    rw [_root_.mul_one, ← map_pow] at e
    rw [hφ e] at hx
    exact hpa (p.isPrime.mem_of_pow_mem n hx)
end GlobalTheory
