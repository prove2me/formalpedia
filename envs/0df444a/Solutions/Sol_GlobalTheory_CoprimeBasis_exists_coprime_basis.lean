-- Prove2me | solution 1 for GlobalTheory.CoprimeBasis.exists_coprime_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:28:17.487969+00:00
-- url     : https://prove2.me/submissions/693f78d6-530f-47d4-a03e-8fff89ec3ed0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemLocDIffSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIndependentBasisCoprime
import Theorems.Thm_GlobalTheory_CoprimeBasis_isTorsionFree_of_addTorsionFree
import Theorems.Thm_GlobalTheory_CoprimeBasis_isCoprime_of_mem_primeTo
import Theorems.Thm_GlobalTheory_Mass_SemiBasis_isPID


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.CoprimeBasis
namespace GlobalTheory.CoprimeBasis
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] [Module.Finite ℤ M] [IsAddTorsionFree M] (N : ℕ), 2 ≤ N → ∃ (r : ℕ) (x : Fin r → M), LinearIndependent (𝓞 F) x ∧ ∃ c : 𝓞 F, c ≠ 0 ∧ IsCoprime c (N : 𝓞 F) ∧ ∀ m : M, c • m ∈ Submodule.span (𝓞 F) (Set.range x) := by
  intro F _ _ M _ _ _ _ N hN
  classical
  set S : Submonoid (𝓞 F) := GlobalTheory.Mass.primeTo (N : 𝓞 F) with hSdef
  have hSle : S ≤ nonZeroDivisors (𝓞 F) := GlobalTheory.Mass.SemiBasis.primeTo_le hN
  haveI : Module.IsTorsionFree (𝓞 F) M := isTorsionFree_of_addTorsionFree M
  haveI : Module.Finite (𝓞 F) M := Module.Finite.of_restrictScalars_finite ℤ (𝓞 F) M
  haveI : IsDomain (Localization S) := IsLocalization.isDomain_localization hSle
  haveI : IsPrincipalIdealRing (Localization S) := by
    haveI := GlobalTheory.Mass.SemiBasis.isPID (K := F) hN
    haveI : IsLocalization S (GlobalTheory.Mass.SemiBasis.A F hN) :=
      Localization.subalgebra.isLocalization_ofField F _ _
    exact IsPrincipalIdealRing.of_surjective
      (IsLocalization.algEquiv S (GlobalTheory.Mass.SemiBasis.A F hN) (Localization S)).toRingHom
      (IsLocalization.algEquiv S (GlobalTheory.Mass.SemiBasis.A F hN) (Localization S)).surjective
  haveI : Module.Finite (Localization S) (LocalizedModule S M) :=
    Module.Finite.of_isLocalizedModule S (LocalizedModule.mkLinearMap S M)
  obtain ⟨r, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := Localization S) (M := LocalizedModule S M)
  have hb : ∀ i, ∃ (m : M) (s : S), b i = LocalizedModule.mk m s := fun i => by
    exact LocalizedModule.induction_on (β := fun y => ∃ (m : M) (s : S), y = LocalizedModule.mk m s)
      (fun m s => ⟨m, s, rfl⟩) (b i)
  choose x s hxs using hb
  have key : ∀ i, (s i : 𝓞 F) • b i = LocalizedModule.mk (x i) 1 := by
    intro i
    rw [hxs i, LocalizedModule.smul'_mk, ← Submonoid.smul_def, LocalizedModule.mk_cancel]
  refine ⟨r, x, ?_, ?_⟩
  · let u : Fin r → (Localization S)ˣ := fun i => (IsLocalization.map_units (Localization S) (s i)).unit
    have hu : LinearIndependent (Localization S) (u • ⇑b) := b.linearIndependent.units_smul u
    have hfx : (u • ⇑b) = LocalizedModule.mkLinearMap S M ∘ x := by
      funext i
      simp only [Pi.smul_apply', Function.comp_apply, LocalizedModule.mkLinearMap_apply, ← key i]
      rw [Units.smul_def, IsUnit.unit_spec, algebraMap_smul]
    rw [hfx] at hu
    have hinj : Function.Injective fun a : 𝓞 F => a • (1 : Localization S) := by
      intro a a' h
      simp only [Algebra.smul_def, mul_one] at h
      exact IsLocalization.injective (Localization S) hSle h
    exact (hu.restrict_scalars hinj).of_comp _
  · set P : Submodule (𝓞 F) M := Submodule.span (𝓞 F) (Set.range x) with hP
    have hloc : ∀ y : LocalizedModule S M, ∃ t : S, ∃ m' ∈ P, (t : 𝓞 F) • y = LocalizedModule.mk m' 1 := by
      intro y
      have hy : y ∈ Submodule.span (Localization S) (Set.range b) := by rw [b.span_eq]; trivial
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        exact ⟨s i, x i, Submodule.subset_span ⟨i, rfl⟩, key i⟩
      | zero => exact ⟨1, 0, P.zero_mem, by simp [LocalizedModule.zero_mk]⟩
      | add y z _ _ hy hz =>
        obtain ⟨t, m, hm, h⟩ := hy
        obtain ⟨t', m', hm', h'⟩ := hz
        refine ⟨t * t', (t' : 𝓞 F) • m + (t : 𝓞 F) • m', P.add_mem (P.smul_mem _ hm) (P.smul_mem _ hm'), ?_⟩
        calc ((t * t' : S) : 𝓞 F) • (y + z) = (t' : 𝓞 F) • ((t : 𝓞 F) • y) + (t : 𝓞 F) • ((t' : 𝓞 F) • z) := by
              rw [Submonoid.coe_mul, smul_add, smul_smul, smul_smul, mul_comm (t' : 𝓞 F)]
          _ = _ := by
              rw [h, h', LocalizedModule.smul'_mk, LocalizedModule.smul'_mk, LocalizedModule.mk_add_mk]
              simp
      | smul a y _ hy =>
        obtain ⟨t, m, hm, h⟩ := hy
        obtain ⟨⟨r0, u⟩, hr⟩ := IsLocalization.surj S a
        have hua : (u : 𝓞 F) • a = algebraMap (𝓞 F) (Localization S) r0 := by
          rw [Algebra.smul_def, mul_comm]; exact hr
        refine ⟨u * t, r0 • m, P.smul_mem r0 hm, ?_⟩
        calc ((u * t : S) : 𝓞 F) • (a • y) = ((u : 𝓞 F) • a) • ((t : 𝓞 F) • y) := by
              rw [Submonoid.coe_mul, mul_smul, smul_comm (t : 𝓞 F) a y, smul_assoc]
          _ = LocalizedModule.mk (r0 • m) 1 := by
              rw [hua, h, algebraMap_smul, LocalizedModule.smul'_mk]
    have hgen : ∀ m : M, ∃ t : S, (t : 𝓞 F) • m ∈ P := by
      intro m
      obtain ⟨t, m', hm', h⟩ := hloc (LocalizedModule.mk m 1)
      rw [LocalizedModule.smul'_mk, LocalizedModule.mk_eq] at h
      obtain ⟨u, hu⟩ := h
      simp only [one_smul, Submonoid.smul_def] at hu
      refine ⟨u * t, ?_⟩
      rw [Submonoid.coe_mul, mul_smul, hu]
      exact P.smul_mem _ hm'
    obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := 𝓞 F) (M := M)
    choose t ht using fun j => hgen (g j)
    refine ⟨((∏ j, t j : S) : 𝓞 F), ?_, ?_, ?_⟩
    · exact nonZeroDivisors.ne_zero (hSle (∏ j, t j).2)
    · exact isCoprime_of_mem_primeTo (∏ j, t j).2
    · intro m
      have hle : Submodule.span (𝓞 F) (Set.range g) ≤
          P.comap (LinearMap.lsmul (𝓞 F) M ((∏ j, t j : S) : 𝓞 F)) := by
        rw [Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        show ((∏ j, t j : S) : 𝓞 F) • g j ∈ P
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), Submonoid.coe_mul, mul_smul]
        exact P.smul_mem _ (ht j)
      rw [hg] at hle
      exact hle Submodule.mem_top
end GlobalTheory.CoprimeBasis
