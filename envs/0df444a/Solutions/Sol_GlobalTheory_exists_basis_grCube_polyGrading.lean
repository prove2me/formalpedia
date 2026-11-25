-- Prove2me | solution 1 for GlobalTheory.exists_basis_grCube_polyGrading
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:07:26.222809+00:00
-- url     : https://prove2.me/submissions/9fb33fa0-1899-4497-b9ea-18795f796b5b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LinearIndependentLaurentMonomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SpanLaurentMonomialEqHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMonomialBasisCechCubePolynomialGrading
import Theorems.Thm_GlobalTheory_exists_xProd_pow_smul_monomial
import Theorems.Thm_GlobalTheory_awayFrac_monomial_congr
import Theorems.Thm_GlobalTheory_exists_laurent_numerator
import Theorems.Thm_GlobalTheory_GrSum_map_of
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
import Theorems.Thm_GlobalTheory_linearIndependent_laurentMonomial
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
import Theorems.Thm_GlobalTheory_locCubeMap_id
import Theorems.Thm_GlobalTheory_span_laurentMonomial_eq_homLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.GrSum.map_of
attribute [local simp] GlobalTheory.Wick.dividedContraction_one
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (n : ℤ), ∃ b : ∀ s : Finset ι, Module.Basis {a : {a : ι → ℤ // ∑ i, a i = n} // Finset.univ.filter (fun i => a.1 i < 0) ⊆ s} R ((grCube ι (polyGrading ι R) n).obj s), ∀ (s t : Finset ι) (h : s ⊆ t) (a : {a : {a : ι → ℤ // ∑ i, a i = n} // Finset.univ.filter (fun i => a.1 i < 0) ⊆ s}), Cube.res (grCube ι (polyGrading ι R) n) h (b s a) = b t ⟨a.1, a.2.trans h⟩ := by
  intro ι _ _ R _ n
  have hiff : ∀ (s : Finset ι) (a : ι → ℤ),
      Finset.univ.filter (fun i => a i < 0) ⊆ s ↔ ∀ i, i ∉ s → 0 ≤ a i := by
    intro s a
    simp only [Finset.subset_iff, Finset.mem_filter, Finset.mem_univ, true_and]
    exact forall_congr' fun i => by rw [← not_lt]; exact not_imp_not.symm
  have key : ∀ s : Finset ι, ∃ b : Module.Basis {a : {a : ι → ℤ // ∑ i, a i = n} //
      Finset.univ.filter (fun i => a.1 i < 0) ⊆ s} R (homLoc (polyGrading ι R) s n),
      ∀ a (k : ℕ) (m : ι →₀ ℕ), (∀ i, (m i : ℤ) = a.1.1 i + if i ∈ s then (k : ℤ) else 0) →
        (b a).1 = awayFrac (MvPolynomial ι R) (xProd R s) k (monomial m 1) := by
    intro s
    choose k m hm using fun a : {a : ι → ℤ // ∑ i, a i = n ∧ ∀ i, i ∉ s → 0 ≤ a i} =>
      exists_laurent_numerator s a.1 a.2.2
    let v := fun a => awayFrac (MvPolynomial ι R) (xProd R s) (k a) (monomial (m a) 1)
    have hv : ∀ a (j : ℕ) (m' : ι →₀ ℕ),
        (∀ i, (m' i : ℤ) = a.1 i + if i ∈ s then (j : ℤ) else 0) →
        v a = awayFrac (MvPolynomial ι R) (xProd R s) j (monomial m' 1) :=
      fun a j m' h => awayFrac_monomial_congr R s a.1 (hm a) h
    let e : {a : ι → ℤ // ∑ i, a i = n ∧ ∀ i, i ∉ s → 0 ≤ a i} ≃
        {a : {a : ι → ℤ // ∑ i, a i = n} // Finset.univ.filter (fun i => a.1 i < 0) ⊆ s} :=
      { toFun := fun a => ⟨⟨a.1, a.2.1⟩, (hiff s a.1).2 a.2.2⟩
        invFun := fun a => ⟨a.1.1, a.1.2, (hiff s a.1.1).1 a.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    refine ⟨((Module.Basis.span (linearIndependent_laurentMonomial ι R s n v hv)).map
      (LinearEquiv.ofEq _ _ (span_laurentMonomial_eq_homLoc ι R s n v hv))).reindex e, fun a j m' h => ?_⟩
    rw [Module.Basis.reindex_apply, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply,
      Module.Basis.span_apply]
    exact hv _ j m' h
  choose b hb using key
  refine ⟨b, fun s t h a => Subtype.ext ?_⟩
  obtain ⟨k, m, hm⟩ := exists_laurent_numerator s a.1.1 ((hiff s _).1 a.2)
  obtain ⟨u, hu, eu⟩ := exists_xProd_pow_smul_monomial R (t \ s) k m
  change locRes X (MvPolynomial ι R) h (b s a).1 = (b t ⟨a.1, a.2.trans h⟩).1
  rw [hb s a k m hm, locRes_awayFrac X h (Finset.prod_sdiff h).symm, eu]
  refine (hb t _ k u fun i => ?_).symm
  have h1 := hu i
  have h2 := hm i
  have h3 := @h i
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all
end GlobalTheory
