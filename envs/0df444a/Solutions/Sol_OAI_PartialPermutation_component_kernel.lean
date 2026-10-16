-- Prove2me | solution 1 for OAI.PartialPermutation.component_kernel
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T21:12:45.550986+00:00
-- url     : https://prove2.me/submissions/94a62453-531a-482a-8be7-9f6cc0774a67

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/JointKernels.lean:L80-L137
-- (upload_full_project.md Phase 4): solution for node OAI.PartialPermutation.component_kernel. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_PartialPermutation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SchurAverage
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ModuleTransport
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Components
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CentralKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CompleteKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RegularRepresentation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Plancherel
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TrivialRepresentation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ConvolutionKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ComponentGeometry
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SmallKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ProjectionCovers
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Restriction
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_IsotypicMatrices
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_IsotypicKernels
import Theorems.Thm_OAI_PartialPermutation_commuting_degrees_dvd_finrank
import Theorems.Thm_OAI_PartialPermutation_exists_degree_le_rpow
import Theorems.Thm_OAI_PartialPermutation_exists_isotypicKernelModel
import Theorems.Thm_OAI_PartialPermutation_group_isotypic_restrict
import Theorems.Thm_OAI_PartialPermutation_subgroup_algebra_commute

-- ---- from OAI.RepresentationTheory.PartialPermutation.MatrixDegrees ----
namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace PartialPermutation

section MatrixTraces
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

end MatrixTraces

section CommutingDegrees
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {ι : Type*} [DecidableEq ι] (d : ι → ℕ) (hd : ∀ i, 0 < d i)
    (A : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ →ₐ[ℂ] Module.End ℂ V)
    (hcomm : ∀ i j, i ≠ j → ∀ X Y, Commute (A i X) (A j Y))

include hd A hcomm

lemma commuting_degrees_le_finrank [Nontrivial V] (s : Finset ι) :
    (∏ i ∈ s, d i) ≤ Module.finrank ℂ V :=
  Nat.le_of_dvd (Module.finrank_pos (R := ℂ))
    (commuting_degrees_dvd_finrank d hd A hcomm s)

end CommutingDegrees

end PartialPermutation

end

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.Restriction ----
namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

attribute [local instance] Classical.propDecidable
open scoped BigOperators
open scoped MonoidAlgebra BigOperators

namespace PartialPermutation

section GroupRestriction
variable {G M : Type*} [Group G] [AddCommGroup M] [Module ℂ[G] M]

lemma restrictGroupModule_tower [Module ℂ M] [IsScalarTower ℂ ℂ[G] M]
    (H : Subgroup G) :
    letI := restrictGroupModule (M := M) H
    IsScalarTower ℂ ℂ[H] M := by
  let := restrictGroupModule (M := M) H
  apply IsScalarTower.of_algebraMap_smul
  intro c x
  change (MonoidAlgebra.mapDomainAlgHom ℂ ℂ H.subtype (algebraMap ℂ ℂ[H] c)) • x = c • x
  rw [AlgHom.commutes, algebraMap_smul]

end GroupRestriction
end PartialPermutation

end

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.BlockSubgroups ----
namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

attribute [local instance] Classical.propDecidable
open scoped MonoidAlgebra BigOperators
open scoped BigOperators

namespace PartialPermutation

lemma jointFactors_generate {G : Type*} [Group G] {b : ℕ} (H : Fin b → Subgroup G) :
    ⨆ i, (H i).subgroupOf (⨆ j, H j) = ⊤ := by
  apply Subgroup.map_subtype_inj.mp
  rw [Subgroup.map_iSup]
  simp only [Subgroup.map_subgroupOf_eq_of_le (le_iSup H _),
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

lemma jointFactors_commute {G : Type*} [Group G] {b : ℕ} (H : Fin b → Subgroup G)
    (h : ∀ i j, i ≠ j → ∀ g ∈ H i, ∀ k ∈ H j, Commute g k) :
    ∀ i j, i ≠ j → ∀ g ∈ (H i).subgroupOf (⨆ j, H j),
      ∀ k ∈ (H j).subgroupOf (⨆ j, H j), Commute g k := by
  intro i j hij g hg k hk
  apply Subtype.ext
  exact h i j hij g hg k hk

end PartialPermutation

end

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.JointKernels ----
namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

attribute [local instance] Classical.propDecidable
open scoped MonoidAlgebra BigOperators
open scoped BigOperators

namespace PartialPermutation
open scoped MonoidAlgebra BigOperators ComplexConjugate

noncomputable section

lemma isotypic_joint_kernels {G M : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    [Module ℂ[G] M] [IsScalarTower ℂ ℂ[G] M]
    [FiniteDimensional ℂ M] [Nontrivial M]
    {b : ℕ} (H : Fin b → Subgroup G) (hgen : ⨆ i, H i = ⊤)
    (hcomm : ∀ i j, i ≠ j → ∀ g ∈ H i, ∀ k ∈ H j, Commute g k)
    (h : IsIsotypic ℂ[G] M)
    (hu : ∀ (g : G) (x y : M), inner ℂ ((MonoidAlgebra.single g (1 : ℂ)) • x)
      ((MonoidAlgebra.single g (1 : ℂ)) • y) = inner ℂ x y) :
    ∃ d : Fin b → ℕ, (∀ i, 0 < d i) ∧ (∏ i, d i) ≤ Module.finrank ℂ M ∧
      ∀ i, ∃ k : H i → ℂ,
        (∑ g, ‖k g‖^2 = (d i : ℝ)^2 / Fintype.card (H i)) ∧
        (∀ g, k g⁻¹ = conj (k g)) ∧
        (∀ x : M, ∑ g, k g • (MonoidAlgebra.single (g : G) (1 : ℂ)) • x = x) := by
  classical
  let (i : Fin b) : Module ℂ[H i] M := restrictGroupModule (H i)
  let (i : Fin b) : IsScalarTower ℂ ℂ[H i] M := restrictGroupModule_tower (H i)
  have hmodels (i : Fin b) : Nonempty (IsotypicKernelModel (H i) M) := by
    apply exists_isotypicKernelModel (group_isotypic_restrict H hgen hcomm h i)
    intro g x y
    change inner ℂ ((MonoidAlgebra.mapDomainAlgHom ℂ ℂ (H i).subtype
      (MonoidAlgebra.single g (1 : ℂ))) • x)
      ((MonoidAlgebra.mapDomainAlgHom ℂ ℂ (H i).subtype
      (MonoidAlgebra.single g (1 : ℂ))) • y) = _
    simpa [MonoidAlgebra.mapDomainAlgHom] using hu g x y
  let F (i : Fin b) := Classical.choice (hmodels i)
  have hAcomm (i j : Fin b) (hij : i ≠ j) (X Y) : Commute ((F i).lift X) ((F j).lift Y) := by
    obtain ⟨r, hr⟩ := (F i).lift_image X
    obtain ⟨s, hs⟩ := (F j).lift_image Y
    rw [hr, hs]
    have he (i : Fin b) (r : ℂ[H i]) : Algebra.lsmul ℂ ℂ M r =
        Algebra.lsmul ℂ ℂ M (MonoidAlgebra.mapDomainAlgHom ℂ ℂ (H i).subtype r) := by
      ext x
      rfl
    rw [he i r, he j s]
    exact (subgroup_algebra_commute (H i) (H j) (hcomm i j hij) r s).map
      (Algebra.lsmul ℂ ℂ M : ℂ[G] →ₐ[ℂ] Module.End ℂ M)
  refine ⟨fun i => (F i).degree, fun i => (F i).degree_pos, ?_, ?_⟩
  · exact commuting_degrees_le_finrank (fun i => (F i).degree)
      (fun i => (F i).degree_pos) (fun i => (F i).lift) hAcomm Finset.univ
  · intro i
    refine ⟨(F i).kernel, (F i).kernel_norm, (F i).kernel_inv, ?_⟩
    intro x
    have ht := (F i).kernel_action x
    change ∑ g, (F i).kernel g • (MonoidAlgebra.mapDomainAlgHom ℂ ℂ (H i).subtype
      (MonoidAlgebra.single g (1 : ℂ))) • x = x at ht
    simpa [MonoidAlgebra.mapDomainAlgHom] using ht

section ComponentKernel
variable {G V : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) {b : ℕ} (H : Fin b → Subgroup G)

lemma component_kernel (hb : 0 < b) (hD : 0 < Module.finrank ℂ V) (hρ : IsUnitary ρ)
    (hcomm : ∀ i j, i ≠ j → ∀ g ∈ H i, ∀ k ∈ H j, Commute g k)
    (c : isotypicComponents ℂ[↥(⨆ i, H i)] (Representation.asModule (ρ.comp (⨆ i, H i).subtype))) :
    ∃ i, ∃ d : ℕ, ∃ k : H i → ℂ,
      (d : ℝ) ≤ (Module.finrank ℂ V : ℝ) ^ (1 / (b : ℝ)) ∧
      (∑ g, ‖k g‖^2 = (d : ℝ)^2 / Fintype.card (H i)) ∧
      (∀ g, k g⁻¹ = conj (k g)) ∧
      (∀ x ∈ componentSpace (ρ.comp (⨆ i, H i).subtype) c,
        complexFourier (ρ.comp (H i).subtype) k x = x) := by
  classical
  let J := ⨆ i, H i
  let ρJ : Representation ℂ J V := ρ.comp J.subtype
  let : NormedAddCommGroup c.val :=
    inferInstanceAs (NormedAddCommGroup (componentSpace ρJ c))
  let : InnerProductSpace ℂ c.val :=
    inferInstanceAs (InnerProductSpace ℂ (componentSpace ρJ c))
  let : FiniteDimensional ℂ c.val :=
    inferInstanceAs (FiniteDimensional ℂ (componentSpace ρJ c))
  let inc : c.val →ₗ[ℂ] V := c.val.subtype.restrictScalars ℂ
  have hinc (g : J) (x : c.val) :
      inc ((MonoidAlgebra.single g (1 : ℂ)) • x) = ρ (g : G) (inc x) := by
    change ρJ.asAlgebraHom (MonoidAlgebra.single g 1) (inc x) = _
    rw [Representation.asAlgebraHom_single, one_smul]
    rfl
  have hu : ∀ (g : J) (x y : c.val),
      inner ℂ ((MonoidAlgebra.single g (1 : ℂ)) • x)
        ((MonoidAlgebra.single g (1 : ℂ)) • y) = inner ℂ x y := by
    intro g x y
    change inner ℂ (inc ((MonoidAlgebra.single g (1 : ℂ)) • x))
      (inc ((MonoidAlgebra.single g (1 : ℂ)) • y)) = inner ℂ (inc x) (inc y)
    rw [hinc, hinc]
    exact hρ (g : G) (inc x) (inc y)
  obtain ⟨d, hdpos, hprod, hkernel⟩ := isotypic_joint_kernels
    (M := c.val) (fun i => (H i).subgroupOf J)
    (jointFactors_generate H) (jointFactors_commute H hcomm)
    (IsIsotypic.isotypicComponents c.property) hu
  have hdim : Module.finrank ℂ c.val ≤ Module.finrank ℂ V :=
    Submodule.finrank_le (componentSpace ρJ c)
  obtain ⟨i, hi⟩ := exists_degree_le_rpow hb hD d (hprod.trans hdim)
  obtain ⟨k, hk, hki, hka⟩ := hkernel i
  let e := Subgroup.subgroupOfEquivOfLe (le_iSup H i)
  let k' : H i → ℂ := fun g => k (e.symm g)
  refine ⟨i, d i, k', hi, ?_, ?_, ?_⟩
  · have he : ∑ g, ‖k' g‖^2 = ∑ g, ‖k g‖^2 :=
      Fintype.sum_equiv e.symm.toEquiv _ _ (fun g => rfl)
    rw [he, hk, Fintype.card_congr e.toEquiv]
  · intro g
    simp only [k', map_inv, hki]
  · intro x hx
    have ht := congrArg inc (hka ⟨x, hx⟩)
    have hix : inc ⟨x, hx⟩ = x := rfl
    have ht' : ∑ g : (H i).subgroupOf J, k g • ρ (g.val.val) x = x := by
      simpa only [map_sum, map_smul, hinc, hix] using ht
    rw [complexFourier, LinearMap.sum_apply]
    calc
      _ = ∑ g : (H i).subgroupOf J, k g • ρ (g.val.val) x := by
        exact Fintype.sum_equiv e.symm.toEquiv _ _ (fun g => rfl)
      _ = x := ht'

end ComponentKernel
end
end PartialPermutation

end

end OAI

-- ---- platform node ----
open OAI OAI.PartialPermutation
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical
attribute [local instance] Classical.propDecidable
open scoped MonoidAlgebra BigOperators
open scoped BigOperators
open scoped MonoidAlgebra BigOperators ComplexConjugate


theorem solution : type_of% @_root_.OAI.PartialPermutation.component_kernel := @_root_.OAI.PartialPermutation.component_kernel
