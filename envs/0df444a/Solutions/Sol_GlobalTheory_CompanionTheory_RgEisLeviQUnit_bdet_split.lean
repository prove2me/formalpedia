-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLeviQUnit.bdet_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:44:09.292185+00:00
-- url     : https://prove2.me/submissions/2eb8fc29-c94f-4fd9-bdfd-3367e8c5312f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviQuotientOfBlockDet
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_bdet_val
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_det_range
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_pull_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisLeviQUnit
open PositivityTheory.RgEis
variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {s : Set ι}
  [Fintype ↥sᶜ] [DecidableEq ↥sᶜ] (A : Ad E R) (ε : ℤˣ) (hσ : ∀ x, A.σ (A.σ x) = x)
include hσ
namespace GlobalTheory.CompanionTheory.RgEisLeviQUnit
theorem _root_.solution (p : A.uQ ε s) (hp : (p : A.U ε ι) ∈ A.uQ ε Set.univ) :
    bdet (Sum.inl '' (Set.univ : Set ι)) (p : A.U ε ι).1 =
      bdet (Sum.inl '' s) (p : A.U ε ι).1 *
        bdet (Sum.inl '' (Set.univ : Set ↥sᶜ)) (piQ A ε hσ p).1 := by
  classical
  have hπ := ((pull_mem A ε hσ (p : A.U ε ι)).1 ⟨p.2, hp⟩).2
  refine Units.ext ?_
  rw [Units.val_mul, bdet_val _ _ (Subgroup.mem_subgroupOf.1 hp), bdet_val _ _ (q_stab A ε p),
    bdet_val _ _ (Subgroup.mem_subgroupOf.1 hπ)]
  set g := ((p : A.U ε ι).1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R) with hg
  rw [det_range (Sum.inl : ι → ι ⊕ ι) Sum.inl_injective _ (by simp),
    det_range (fun i : {i // i ∈ s} => (Sum.inl i.1 : ι ⊕ ι)) (fun a b h => Subtype.ext (Sum.inl_injective h)) _
      (by ext x; simp),
    det_range (fun i : {i // ¬ i ∈ s} => (Sum.inl ⟨i.1, i.2⟩ : ↥sᶜ ⊕ ↥sᶜ))
      (fun a b h => Subtype.ext (congrArg Subtype.val (Sum.inl_injective h))) _ (by
        ext x
        constructor
        · rintro ⟨y, -, rfl⟩
          exact ⟨⟨y.1, y.2⟩, rfl⟩
        · rintro ⟨y, rfl⟩
          exact ⟨_, trivial, rfl⟩)]
  have hz : ∀ i, ¬ i ∈ s → ∀ j, j ∈ s → (g.submatrix Sum.inl Sum.inl : Matrix ι ι R) i j = 0 := fun i hi j hj =>
    ((q_stab A ε p) (Sum.inl i) (by
      rintro ⟨k, hk, h⟩
      exact hi (Sum.inl_injective h ▸ hk)) (Sum.inl j) ⟨j, hj, rfl⟩).1
  have := Matrix.twoBlockTriangular_det (g.submatrix Sum.inl Sum.inl : Matrix ι ι R) (fun i => i ∈ s) hz
  rw [this]
  congr! 1
  congr! 1
end GlobalTheory.CompanionTheory.RgEisLeviQUnit
