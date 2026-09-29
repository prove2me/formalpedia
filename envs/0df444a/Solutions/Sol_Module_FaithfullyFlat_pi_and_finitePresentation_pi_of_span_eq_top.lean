-- Prove2me | solution 1 for Module.FaithfullyFlat.pi_and_finitePresentation_pi_of_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/3d9ff01c-44ce-5273-8d45-c920d73dad6b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_FaithfullyFlat_pi_and_finitePresentation_pi_of_span_eq_top

set_option autoImplicit false

open TensorProduct

theorem solution
    {S : Type} [CommRing S] {ι : Type} [Fintype ι] [DecidableEq ι] (g : ι → S) (hg : Ideal.span (Set.range g) = ⊤)
    (C : ι → Type) [∀ i, CommRing (C i)] [∀ i, Algebra S (C i)] [∀ i, Algebra (Localization.Away (g i)) (C i)]
    [∀ i, IsScalarTower S (Localization.Away (g i)) (C i)]
    (hff : ∀ i, Module.FaithfullyFlat (Localization.Away (g i)) (C i))
    (hfp : ∀ i, Algebra.FinitePresentation (Localization.Away (g i)) (C i)) :
    Module.FaithfullyFlat S (∀ i, C i) ∧ Algebra.FinitePresentation S (∀ i, C i) := by
  classical

  have hflat : ∀ i, Module.Flat S (C i) := fun i =>
    haveI : Module.Flat S (Localization.Away (g i)) := IsLocalization.flat _ (Submonoid.powers (g i))
    haveI : Module.Flat (Localization.Away (g i)) (C i) := (hff i).toFlat
    Module.Flat.trans S (Localization.Away (g i)) (C i)
  have hfpS : ∀ i, Algebra.FinitePresentation S (C i) := fun i =>
    haveI : Algebra.FinitePresentation S (Localization.Away (g i)) :=
      IsLocalization.Away.finitePresentation (g i)
    haveI := hfp i
    Algebra.FinitePresentation.trans S (Localization.Away (g i)) (C i)
  refine ⟨?_, inferInstance⟩

  haveI : Module.Flat S (∀ i, C i) :=
    Module.Flat.of_linearEquiv (DirectSum.linearEquivFunOnFintype S ι C).symm
  refine ⟨fun 𝔪 h𝔪 htop => ?_⟩

  obtain ⟨i, hi⟩ : ∃ i, g i ∉ 𝔪 := by
    by_contra hcon
    push Not at hcon
    apply h𝔪.ne_top
    rw [eq_top_iff, ← hg, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hcon i

  have hdisj : Disjoint (↑(Submonoid.powers (g i)) : Set S) ↑𝔪 := by
    rw [Set.disjoint_left]
    rintro x ⟨n, rfl⟩ hx
    exact hi (h𝔪.isPrime.mem_of_pow_mem n hx)
  have hprime : (𝔪.map (algebraMap S (Localization.Away (g i)))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (g i)) (Localization.Away (g i)) 𝔪 h𝔪.isPrime hdisj

  have hne : (𝔪.map (algebraMap S (Localization.Away (g i)))) • (⊤ : Submodule (Localization.Away (g i)) (C i)) ≠ ⊤ :=
    ((Module.FaithfullyFlat.iff_flat_and_proper_ideal _ _).mp (hff i)).2 _ hprime.ne_top
  apply hne

  rw [Ideal.smul_top_eq_map] at htop ⊢
  rw [Submodule.restrictScalars_eq_top_iff] at htop ⊢
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have h1 : (Ideal.map (algebraMap S (∀ i, C i)) 𝔪).map (Pi.evalRingHom C i) = ⊤ := by
    rw [htop, Ideal.map_top]
  rw [Ideal.map_map] at h1
  convert h1 using 2
  ext s
  rfl

end S_Module_FaithfullyFlat_pi_and_finitePresentation_pi_of_span_eq_top
end P2MW
export P2MW.S_Module_FaithfullyFlat_pi_and_finitePresentation_pi_of_span_eq_top (solution)
