-- Prove2me | solution 1 for GlobalTheory.span_range_algebraMap_eq_top_of_tame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:33:47.123272+00:00
-- url     : https://prove2.me/submissions/972af6fe-d709-4f47-9679-0c8333421c52

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulMemSpanInvariantsSup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SubalgebraEqTopOfForallPrimeSmulMemSup
import Theorems.Thm_GlobalTheory_exists_smul_mem_span_invariants_sup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct Pointwise
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (A B R C : Type) [CommRing A] [CommRing B] [CommRing R] [CommRing C] [MulSemiringAction Γ B] [MulSemiringAction Γ C] [Algebra A B] [Algebra A R] [Algebra B C] [Algebra R C] [Algebra A C] [IsScalarTower A B C] [IsScalarTower A R C] [SMulCommClass Γ A B] [SMulCommClass Γ R C] [Algebra.IsInvariant A B Γ] [Algebra.IsInvariant R C Γ], Function.Injective (algebraMap A B) → Function.Injective (algebraMap R C) → (∀ (g : Γ) (b : B), g • algebraMap B C b = algebraMap B C (g • b)) → Module.Finite R C → (∀ q : Ideal B, q.IsPrime → (Nat.card (q.inertia Γ) : B) ∉ q) → (∀ q : Ideal B, q.IsPrime → ∀ g ∈ q.inertia Γ, ∀ c : C, g • c - c ∈ q.map (algebraMap B C)) → Submodule.span B (Set.range (algebraMap R C)) = ⊤ := by
  intro Γ _ _ A B R C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcompat _ htame hin
  classical
  let M : Subalgebra B C := Algebra.adjoin B (Set.range (algebraMap R C))
  have hRM : ∀ r : R, algebraMap R C r ∈ M := fun r => Algebra.subset_adjoin ⟨r, rfl⟩
  letI : Algebra R M := ((algebraMap R C).codRestrict M hRM).toAlgebra
  haveI : IsScalarTower R M C := IsScalarTower.of_algebraMap_eq fun r => rfl
  haveI : Module.Finite M C := Module.Finite.of_restrictScalars_finite R M C
  have hsmulM : ∀ (m : M) (c : C), m • c = (m : C) * c := fun m c => rfl
  have hsmulB : ∀ (b : B) (c : C), b • c = (algebraMap B M b : C) * c := fun b c => by
    rw [Algebra.smul_def]
    rfl
  let P' : Submodule M C := Submodule.span M {1}
  have hmemP' : ∀ c ∈ M, c ∈ P' := by
    intro c hc
    rw [Submodule.mem_span_singleton]
    exact ⟨⟨c, hc⟩, by rw [hsmulM, _root_.mul_one]⟩
  have hcomp : ∀ (g : Γ) (b : B) (x : C), g • (b • x) = (g • b) • (g • x) := by
    intro g b x
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hcompat]
  have hin' : ∀ q : Ideal B, q.IsPrime → ∀ g ∈ q.inertia Γ, ∀ x : C,
      g • x - x ∈ q • (⊤ : Submodule B C) := by
    intro q hq g hg x
    rw [Ideal.smul_top_eq_map]
    exact hin q hq g hg x
  have hloc : ∀ P : Ideal M, P.IsMaximal → (⊤ : Submodule M (C ⧸ P')) ≤ P • ⊤ := by
    intro P hP x _
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective P' x
    haveI : P.IsPrime := hP.isPrime
    have hq : (P.comap (algebraMap B M)).IsPrime := Ideal.comap_isPrime _ _
    obtain ⟨s, hs, hsc⟩ := _root_.GlobalTheory.exists_smul_mem_span_invariants_sup Γ B C hcomp _ hq
      (htame _ hq) (hin' _ hq) c
    have hsmall : ∀ y ∈ Submodule.span B {y : C | ∀ g : Γ, g • y = y} ⊔
        (P.comap (algebraMap B M)) • (⊤ : Submodule B C),
        (Submodule.Quotient.mk y : C ⧸ P') ∈ P • (⊤ : Submodule M (C ⧸ P')) := by
      intro y hy
      obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
      rw [Submodule.Quotient.mk_add]
      refine add_mem ?_ ?_
      · have h1 : y₁ ∈ Subalgebra.toSubmodule M := by
          refine (Submodule.span_le (p := Subalgebra.toSubmodule M)).mpr ?_ hy₁
          intro z hz
          obtain ⟨r, rfl⟩ := Algebra.IsInvariant.isInvariant (A := R) (G := Γ) z hz
          exact hRM r
        rw [(Submodule.Quotient.mk_eq_zero P').mpr (hmemP' _ h1)]
        exact zero_mem _
      · refine Submodule.smul_induction_on
          (p := fun y => (Submodule.Quotient.mk y : C ⧸ P') ∈ P • (⊤ : Submodule M (C ⧸ P'))) hy₂ ?_ ?_
        · intro b hb z _
          rw [show b • z = (algebraMap B M b) • z by rw [hsmulM, hsmulB],
            Submodule.Quotient.mk_smul]
          exact Submodule.smul_mem_smul hb trivial
        · intro z w hz hw
          simp only [Submodule.Quotient.mk_add]
          exact add_mem hz hw
    have hσ : algebraMap B M s ∉ P := hs
    obtain ⟨u, i, hi, hui⟩ := hP.exists_inv hσ
    have hx : (Submodule.Quotient.mk c : C ⧸ P') =
        u • (Submodule.Quotient.mk (s • c) : C ⧸ P') + i • Submodule.Quotient.mk c := by
      rw [show s • c = (algebraMap B M s) • c by rw [hsmulM, hsmulB], Submodule.Quotient.mk_smul,
        smul_smul, ← add_smul, hui, one_smul]
    rw [hx]
    exact add_mem (Submodule.smul_mem _ _ (hsmall _ hsc)) (Submodule.smul_mem_smul hi trivial)
  have hann : Module.annihilator M (C ⧸ P') = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul P
      (⊤ : Submodule M (C ⧸ P')) Module.Finite.fg_top (hloc P hP)
    have hrP : r ∈ P := hle (Module.mem_annihilator.mpr fun n => hr n trivial)
    have h1 : (1 : M) ∈ P := by simpa using P.sub_mem hrP hr1
    exact hP.ne_top ((Ideal.eq_top_iff_one P).mpr h1)
  refine eq_top_iff.mpr fun c _ => ?_
  have h1 : (1 : M) ∈ Module.annihilator M (C ⧸ P') := by
    rw [hann]
    exact Submodule.mem_top
  have hc0 : (Submodule.Quotient.mk c : C ⧸ P') = 0 := by
    have h := Module.mem_annihilator.mp h1 (Submodule.Quotient.mk c)
    rwa [one_smul] at h
  obtain ⟨m, hm⟩ := Submodule.mem_span_singleton.mp ((Submodule.Quotient.mk_eq_zero P').mp hc0)
  rw [hsmulM, _root_.mul_one] at hm
  have hcM : c ∈ Subalgebra.toSubmodule M := hm ▸ m.2
  rw [Algebra.adjoin_eq_span] at hcM
  refine Submodule.span_mono ?_ hcM
  intro z hz
  have hcl : Submonoid.closure (Set.range (algebraMap R C)) ≤
      (algebraMap R C).rangeS.toSubmonoid :=
    Submonoid.closure_le.mpr fun w ⟨r, hr⟩ => ⟨r, hr⟩
  obtain ⟨r, hr⟩ := hcl hz
  exact ⟨r, hr⟩
end _root_.GlobalTheory
end GlobalTheory
