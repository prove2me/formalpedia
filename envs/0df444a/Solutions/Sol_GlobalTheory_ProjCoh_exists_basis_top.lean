-- Prove2me | solution 1 for GlobalTheory.ProjCoh.exists_basis_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:43:35.45386+00:00
-- url     : https://prove2.me/submissions/d48c831f-2da7-4425-937a-a01d581897fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfMonomialBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_TopClassSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMonomialBasisCechCubePolynomialGrading
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexPolyGradingFiniteExact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NonemptyBasisPolyGrading
import Theorems.Thm_GlobalTheory_ProjCoh_topCech_surjective
import Theorems.Thm_GlobalTheory_ProjCoh_topCech_eq_zero_iff
import Theorems.Thm_GlobalTheory_CubeTop_topTerm_res_mem
import Theorems.Thm_GlobalTheory_Cube_SemiHom_homology_cechClass
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
attribute [local simp] GlobalTheory.Cube.SemiHom.homology_cechClass
attribute [local simp] GlobalTheory.GrSum.map_of
attribute [local simp] GlobalTheory.Wick.dividedContraction_one
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id



set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.ProjCoh
variable {ι : Type} [LinearOrder ι] [Fintype ι] {R : Type} [CommRing R]
namespace GlobalTheory.ProjCoh
theorem _root_.solution {κ : Type} (T : κ → Finset ι) (A : Cube.{0} ι R)
    (b : ∀ s : Finset ι, Module.Basis {a : κ // T a ⊆ s} R (A.obj s))
    (hb : ∀ (s t : Finset ι) (h : s ⊆ t) (a : {a : κ // T a ⊆ s}),
      Cube.res A h (b s a) = b t ⟨a.1, a.2.trans h⟩) {N : ℕ} (hN : Fintype.card ι = N + 1 + 1) :
    ∃ c : Module.Basis {a : κ // T a = Finset.univ} R ((cechComplex A).homology (N + 1)),
      ∀ a, c a = topCech A hN (b Finset.univ ⟨a.1, Finset.subset_univ _⟩) := by
  classical
  let j : {a : κ // T a = Finset.univ} → {a : κ // T a ⊆ Finset.univ} :=
    fun a => ⟨a.1, Finset.subset_univ _⟩
  have hj : Function.Injective j := fun a a' h => Subtype.ext (congrArg (·.1) h)
  have h0 : ∀ (a) (i : ι) (x : A.obj (Finset.univ.erase i)),
      (b Finset.univ).coord (j a) (Cube.res A (Finset.erase_subset i _) x) = 0 := fun a i x => by
    have : (b Finset.univ).coord (j a) ∘ₗ Cube.res A (Finset.erase_subset i _) = 0 :=
      (b _).ext fun a' => by
        rw [LinearMap.comp_apply, hb, Module.Basis.coord_apply, Module.Basis.repr_self,
          Finsupp.single_eq_of_ne, LinearMap.zero_apply]
        intro e
        have h1 := a'.2
        rw [← show a.1 = a'.1 from congrArg (·.1) e, a.2] at h1
        simpa using h1 (Finset.mem_univ i)
    exact congr($this x)
  have hli : LinearIndependent R (topCech A hN ∘ (b Finset.univ ∘ j)) := by
    refine ((b Finset.univ).linearIndependent.comp j hj).map (Submodule.disjoint_def.2 ?_)
    intro z hz hz'
    obtain ⟨y, hy⟩ := (topCech_eq_zero_iff A hN z).1 hz'
    have e := congrFun hy ⟨Finset.univ, hN⟩
    rw [Cube.d_apply] at e
    replace e := e.trans (Cube.res_self A _ z)
    rw [Set.range_comp, Module.Basis.mem_span_image] at hz
    refine (b _).ext_elem fun a => ?_
    rw [map_zero, Finsupp.zero_apply]
    by_contra ha
    obtain ⟨a, rfl⟩ := hz (Finsupp.mem_support_iff.2 ha)
    refine ha ?_
    rw [← Module.Basis.coord_apply, ← e, map_sum]
    exact Finset.sum_eq_zero fun i _ => by rw [map_zsmul, h0, smul_zero]
  refine ⟨Module.Basis.mk hli ?_, fun a => Module.Basis.mk_apply _ _ a⟩
  rw [← LinearMap.range_eq_top.2 (topCech_surjective A hN), LinearMap.range_eq_map,
    ← (b Finset.univ).span_eq, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
  by_cases h : T a.1 = Finset.univ
  · exact Submodule.subset_span ⟨⟨a.1, h⟩, rfl⟩
  · obtain ⟨i, hi⟩ : ∃ i, i ∉ T a.1 := by
      simpa [Finset.eq_univ_iff_forall] using h
    have := (topCech_eq_zero_iff A hN _).2 (CubeTop.topTerm_res_mem A hN i
      (b _ ⟨a.1, Finset.subset_erase.2 ⟨Finset.subset_univ _, hi⟩⟩))
    rw [hb] at this
    rw [this]
    exact zero_mem _
end GlobalTheory.ProjCoh
