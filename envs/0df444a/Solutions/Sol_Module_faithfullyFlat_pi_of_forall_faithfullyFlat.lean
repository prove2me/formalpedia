-- Prove2me | solution 1 for Module.faithfullyFlat_pi_of_forall_faithfullyFlat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/382597a7-74a9-5c63-95f9-09c356a49214

import Mathlib
import Theorems.Thm_Module_faithfullyFlat_pi_of_forall_faithfullyFlat_localizationAway_of_span_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_faithfullyFlat_pi_of_forall_faithfullyFlat

set_option autoImplicit false

namespace FFPI

variable {k : ℕ} (C : Fin k → Type) [∀ i, CommRing (C i)]

def e (i : Fin k) : (∀ i, C i) := Pi.single i 1

theorem span_e_eq_top : Ideal.span (Set.range (e C)) = ⊤ := by
  classical
  rw [Ideal.eq_top_iff_one]
  have h1 : (1 : ∀ i, C i) = ∑ i, e C i := by
    simp only [e]
    exact (Finset.univ_sum_single (1 : ∀ i, C i)).symm
  rw [h1]
  exact Ideal.sum_mem _ fun i _ => Ideal.subset_span ⟨i, rfl⟩

abbrev algC (i : Fin k) : Algebra (∀ i, C i) (C i) := (Pi.evalRingHom C i).toAlgebra

theorem isLocalization_e (i : Fin k) :
    letI := algC C i
    IsLocalization (Submonoid.powers (e C i)) (C i) := by
  classical
  letI := algC C i
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hy
    show IsUnit ((Pi.evalRingHom C i) (e C i ^ n))
    rw [map_pow]
    simp [e]
  · intro z
    refine ⟨(Pi.single i z, 1), ?_⟩
    show z * (Pi.evalRingHom C i) 1 = (Pi.evalRingHom C i) (Pi.single i z)
    simp
  · intro x y hxy
    refine ⟨⟨e C i, Submonoid.mem_powers _⟩, ?_⟩
    change x i = y i at hxy
    funext j
    show Pi.single i (1 : C i) j * x j = Pi.single i (1 : C i) j * y j
    by_cases hj : j = i
    · subst hj; simp [hxy]
    · simp [Pi.single_eq_of_ne hj]

end FFPI

open FFPI in
theorem solution
    {k : ℕ} (C : Fin k → Type) [∀ i, CommRing (C i)] (D : Fin k → Type) [∀ i, CommRing (D i)] [∀ i, Algebra (C i) (D i)]
    [inst : Algebra (∀ i, C i) (∀ i, D i)]
    (halg : ∀ (i : Fin k) (x : ∀ i, C i), algebraMap (∀ i, C i) (∀ i, D i) x i = algebraMap (C i) (D i) (x i))
    (hff : ∀ i, Module.FaithfullyFlat (C i) (D i)) :
    @Module.FaithfullyFlat (∀ i, C i) (∀ i, D i) _ _ inst.toModule := by
  classical

  letI algD : ∀ i, Algebra (∀ i, C i) (D i) := fun i => ((algebraMap (C i) (D i)).comp (Pi.evalRingHom C i)).toAlgebra

  have hinst : inst = Pi.algebra (Fin k) D := by
    refine Algebra.algebra_ext _ _ fun x => ?_
    funext i
    rw [halg i x]
    rfl
  subst hinst

  letI algC' : ∀ i, Algebra (∀ i, C i) (C i) := fun i => algC C i
  haveI hloc : ∀ i, IsLocalization (Submonoid.powers (e C i)) (C i) := fun i => isLocalization_e C i
  let θ : ∀ i, Localization.Away (e C i) ≃ₐ[∀ i, C i] C i := fun i =>
    Localization.algEquiv (Submonoid.powers (e C i)) (C i)

  letI algLC : ∀ i, Algebra (Localization.Away (e C i)) (C i) := fun i => (θ i).toRingHom.toAlgebra
  letI algLD : ∀ i, Algebra (Localization.Away (e C i)) (D i) := fun i =>
    ((algebraMap (C i) (D i)).comp (θ i).toRingHom).toAlgebra
  haveI : ∀ i, IsScalarTower (Localization.Away (e C i)) (C i) (D i) := fun i =>
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : ∀ i, IsScalarTower (∀ i, C i) (Localization.Away (e C i)) (D i) := fun i =>
    IsScalarTower.of_algebraMap_eq fun x => by
      show ((algebraMap (C i) (D i)).comp (Pi.evalRingHom C i)) x =
        ((algebraMap (C i) (D i)).comp (θ i).toRingHom) (algebraMap (∀ i, C i) (Localization.Away (e C i)) x)
      simp only [RingHom.coe_comp, Function.comp_apply]
      congr 1
      exact ((θ i).commutes x).symm

  haveI hffC : ∀ i, Module.FaithfullyFlat (Localization.Away (e C i)) (C i) := fun i =>
    Module.FaithfullyFlat.of_linearEquiv (R := Localization.Away (e C i)) (M := Localization.Away (e C i))
      { toFun := (θ i).symm
        map_add' := fun a b => map_add _ a b
        map_smul' := fun l c => by
          show (θ i).symm ((θ i) l * c) = l * (θ i).symm c
          rw [map_mul, AlgEquiv.symm_apply_apply]
        invFun := θ i
        left_inv := fun c => (θ i).apply_symm_apply c
        right_inv := fun l => (θ i).symm_apply_apply l }

  haveI hffD : ∀ i, Module.FaithfullyFlat (Localization.Away (e C i)) (D i) := fun i =>
    haveI := hff i
    Module.FaithfullyFlat.trans (Localization.Away (e C i)) (C i) (D i)
  exact Module.faithfullyFlat_pi_of_forall_faithfullyFlat_localizationAway_of_span_eq_top (e C) (span_e_eq_top C) D hffD

end S_Module_faithfullyFlat_pi_of_forall_faithfullyFlat
end P2MW
export P2MW.S_Module_faithfullyFlat_pi_of_forall_faithfullyFlat (solution)
