-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.exists_eq_algebraMap_sections_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/0d12239f-f30a-5257-9224-ee041ad8bd51

import Mathlib
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_cechFinrank_unit_zero_eq_one
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_eq_algebraMap_sections_top
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

set_option maxHeartbeats 3200000 in
theorem solution
    (K : Type u) [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (hA : AbelianSchemePropertyBundle K f) (𝒦 : A.OrderedAffineCover) (s : Γ(A, ⊤)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f ⊤
    ∃ c : K, s = algebraMap K Γ(A, ⊤) c := by
  classical
  letI instK : ∀ U : A.Opens, Algebra K Γ(A, U) := fun U => Scheme.TwoAffineOpenCover.algebraOfHom f U
  let F := OModulePresheaf.unit f

  let ρ : Γ(A, ⊤) →ₗ[K] F.cochain 𝒦 0 :=
    LinearMap.pi fun t => F.res (le_top : 𝒦.inter t ≤ ⊤)
  have hρ : ∀ (s : Γ(A, ⊤)) (t : 𝒦.Idx 0), ρ s t = (A.presheaf.map (homOfLE (le_top : 𝒦.inter t ≤ ⊤)).op).hom s :=
    fun _ _ => rfl

  have hker : ∀ s : Γ(A, ⊤), ρ s ∈ F.H0 𝒦 := by
    intro s
    rw [LinearMap.mem_ker]
    funext u
    rw [OModulePresheaf.d_apply]
    show ∑ j : Fin 2, ((-1 : ℤ) ^ (j : ℕ)) • F.res (𝒦.inter_le_inter_face u j) (F.res le_top s) = 0
    simp_rw [OModulePresheaf.res_res]
    rw [Fin.sum_univ_two]
    simp
  let ρ' : Γ(A, ⊤) →ₗ[K] ↥(F.H0 𝒦) := LinearMap.codRestrict (F.H0 𝒦) ρ hker

  have hinj : Function.Injective ρ' := by
    intro s t hst
    have hst' : ∀ i : 𝒦.Idx 0, ρ s i = ρ t i := fun i => by
      have := congrArg (fun x : ↥(F.H0 𝒦) => (x : F.cochain 𝒦 0) i) hst
      exact this

    let idx : 𝒦.ι → 𝒦.Idx 0 := fun i => ⟨fun _ => i, fun a b h => absurd h (by omega)⟩
    have hcov : (⊤ : A.Opens) ≤ ⨆ i : 𝒦.ι, 𝒦.inter (idx i) := by
      rw [← 𝒦.iSup_eq_top]
      refine iSup_le fun i => ?_
      refine le_trans ?_ (le_iSup (fun i => 𝒦.inter (idx i)) i)
      exact le_iInf fun _ => le_rfl
    exact TopCat.Sheaf.eq_of_locally_eq' A.sheaf (fun i : 𝒦.ι => 𝒦.inter (idx i)) ⊤ (fun i => homOfLE le_top) hcov s t
      (fun i => hst' (idx i))

  have h1 : Module.finrank K ↥(F.H0 𝒦) = 1 := by
    have := GoodReductionJacobian.AbelianSchemePropertyBundle.cechFinrank_unit_zero_eq_one K f hA 𝒦
    rwa [OModulePresheaf.cechFinrank_zero] at this
  haveI : Module.Finite K ↥(F.H0 𝒦) := Module.finite_of_finrank_pos (by rw [h1]; exact one_pos)
  haveI : Module.Finite K Γ(A, ⊤) := Module.Finite.of_injective ρ' hinj
  have hle : Module.finrank K Γ(A, ⊤) ≤ 1 := h1 ▸ LinearMap.finrank_le_finrank_of_injective hinj

  rcases Nat.lt_or_ge 0 (Module.finrank K Γ(A, ⊤)) with hpos | hzero
  · haveI : Nontrivial Γ(A, ⊤) := Module.finrank_pos_iff.mp hpos
    have hinjK : Function.Injective (Algebra.linearMap K Γ(A, ⊤)) := (algebraMap K Γ(A, ⊤)).injective
    have hrange : LinearMap.range (Algebra.linearMap K Γ(A, ⊤)) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [LinearMap.finrank_range_of_inj hinjK, Module.finrank_self]
      omega
    have : s ∈ LinearMap.range (Algebra.linearMap K Γ(A, ⊤)) := by rw [hrange]; trivial
    obtain ⟨c, hc⟩ := this
    exact ⟨c, hc.symm⟩
  · have h0 : Module.finrank K Γ(A, ⊤) = 0 := by omega
    haveI : Subsingleton Γ(A, ⊤) := Module.finrank_zero_iff.mp h0
    exact ⟨0, Subsingleton.elim _ _⟩

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_eq_algebraMap_sections_top
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_eq_algebraMap_sections_top (solution)
