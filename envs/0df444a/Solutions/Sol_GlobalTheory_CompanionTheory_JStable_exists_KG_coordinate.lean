-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.JStable.exists_KG_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:32:18.892526+00:00
-- url     : https://prove2.me/submissions/2680928c-3040-415e-a0ef-fc4797054695

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ExistsOrthogonalHermitianSubspace
import Theorems.Thm_GlobalTheory_CompanionTheory_JStable_exists_adapted_onb
import Theorems.Thm_GlobalTheory_CompanionTheory_JStable_extendByZero_apply_of_ne
import Theorems.Thm_GlobalTheory_CompanionTheory_JStable_extendByZero_restrict_eigen_projection
import Theorems.Thm_GlobalTheory_CompanionTheory_JStable_eq_extendByZero_restrict_sum
import Theorems.Thm_GlobalTheory_CompanionTheory_JStable_sum_extendByZero_fin_eq_sum_of_eq
import Theorems.Thm_Formalism_REAL_mem_KG


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.JStable
variable {n : ℕ} (ε : Fin n → Bool)
namespace GlobalTheory.CompanionTheory.JStable
theorem _root_.solution (W : Submodule ℂ (Fin n → ℂ))
    (hW : ∀ v ∈ W, Formalism.REAL.Jm ε *ᵥ v ∈ W) :
    ∃ (k : Formalism.REAL.KG ε) (S : Set (Fin n)),
      W = (Submodule.span ℂ (Set.range fun j : S => (Pi.single (j : Fin n) (1 : ℂ) : Fin n → ℂ))).map
        (Formalism.REAL.toMK k).mulVecLin := by
  classical
  choose b T hT using fun s : Bool => exists_adapted_onb (W.comap (ext0 ε s))
  have hres : ∀ (s : Bool) (v : Fin n → ℂ), v ∈ W → res0 ε s v ∈ W.comap (ext0 ε s) := by
    intro s v hv
    rw [Submodule.mem_comap, extendByZero_restrict_eigen_projection]
    exact W.smul_mem _ (W.add_mem hv (W.smul_mem _ (hW v hv)))
  have hdecomp : W = (W.comap (ext0 ε true)).map (ext0 ε true) ⊔
      (W.comap (ext0 ε false)).map (ext0 ε false) := by
    refine le_antisymm (fun v hv => ?_) (sup_le (Submodule.map_le_iff_le_comap.2 le_rfl)
      (Submodule.map_le_iff_le_comap.2 le_rfl))
    rw [eq_extendByZero_restrict_sum ε v]
    exact Submodule.add_mem_sup (Submodule.mem_map_of_mem (hres true v hv))
      (Submodule.mem_map_of_mem (hres false v hv))
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin n) (Fin n) ℂ,
      ∀ i j, M i j = ext0 ε (ε j) (b (ε j) ⟨j, rfl⟩) i :=
    ⟨Matrix.of fun i j => ext0 ε (ε j) (b (ε j) ⟨j, rfl⟩) i, fun _ _ => rfl⟩
  have hcol : ∀ (s : Bool) (i' : {i : Fin n // ε i = s}) (a : Fin n),
      M a i'.1 = ext0 ε s (b s i') a := by
    rintro s ⟨j, rfl⟩ a
    exact hM a j
  have hMM : Mᴴ * M = 1 := by
    ext j l
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    by_cases hjl : ε j = ε l
    · have h1 : ∀ a, M a j = ext0 ε (ε j) (b (ε j) ⟨j, rfl⟩) a := fun a => hcol (ε j) ⟨j, rfl⟩ a
      have h2 : ∀ a, M a l = ext0 ε (ε j) (b (ε j) ⟨l, hjl.symm⟩) a :=
        fun a => hcol (ε j) ⟨l, hjl.symm⟩ a
      simp only [h1, h2]
      rw [sum_extendByZero_fin_eq_sum_of_eq, orthonormal_iff_ite.1 (b (ε j)).orthonormal]
      simp only [Subtype.mk.injEq]
    · have hne : j ≠ l := fun h => hjl (h ▸ rfl)
      rw [if_neg hne]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      by_cases hi : ε i = ε j
      · rw [hM i l, extendByZero_apply_of_ne ε _ (fun h => hjl (hi.symm.trans h)), mul_zero]
      · rw [hM i j, extendByZero_apply_of_ne ε _ hi, star_zero, zero_mul]
  have hMM' : M * Mᴴ = 1 := mul_eq_one_comm.1 hMM
  have hJ : M * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * M := by
    have hJd : Formalism.REAL.Jm ε = Matrix.diagonal (fun a => if ε a then (1 : ℂ) else -1) := rfl
    ext i j
    rw [hJd, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hi : ε i = ε j
    · simp only [hi]
      ring
    · rw [hM i j, extendByZero_apply_of_ne ε _ hi]
      ring
  have hunit : M ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    exact hMM
  let u : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨M, Mᴴ, hMM', hMM⟩
  have hUJ : u ∈ Formalism.REAL.UJ ε := by
    show Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε
    rw [Matrix.mul_assoc, ← hJ, ← Matrix.mul_assoc, hMM, Matrix.one_mul]
  let gu : Formalism.REAL.UJ ε := ⟨u, hUJ⟩
  have hK : M ∈ Formalism.REAL.Kset ε := ⟨hunit, hJ⟩
  let k : Formalism.REAL.KG ε := ⟨gu, (Formalism.REAL.mem_KG ε gu).2 hK⟩
  let S : Set (Fin n) := {j | (⟨j, rfl⟩ : {i : Fin n // ε i = ε j}) ∈ T (ε j)}
  refine ⟨k, S, ?_⟩
  change W = (Submodule.span ℂ (Set.range fun j : S => (Pi.single (j : Fin n) (1 : ℂ) : Fin n → ℂ))).map
    M.mulVecLin
  have hMcol : ∀ (s : Bool) (i' : {i : Fin n // ε i = s}),
      M *ᵥ Pi.single i'.1 1 = ext0 ε s (b s i') := by
    intro s i'
    funext a
    rw [Matrix.mulVec_single_one, Matrix.col_apply, hcol s i' a]
  have hmemS : ∀ (s : Bool) (i' : {i : Fin n // ε i = s}), i' ∈ T s → i'.1 ∈ S := by
    rintro s ⟨j, rfl⟩ hi'
    exact hi'
  have hset : ⇑(ext0 ε true) '' (⇑(b true) '' T true) ∪ ⇑(ext0 ε false) '' (⇑(b false) '' T false) =
      Set.range (⇑M.mulVecLin ∘ fun j : S => (Pi.single (j : Fin n) (1 : ℂ) : Fin n → ℂ)) := by
    ext x
    simp only [Set.mem_union, Set.mem_image, Set.mem_range, Function.comp_apply,
      Matrix.mulVecLin_apply]
    constructor
    · rintro (⟨y, ⟨i', hi', rfl⟩, rfl⟩ | ⟨y, ⟨i', hi', rfl⟩, rfl⟩)
      · exact ⟨⟨i'.1, hmemS true i' hi'⟩, hMcol true i'⟩
      · exact ⟨⟨i'.1, hmemS false i' hi'⟩, hMcol false i'⟩
    · rintro ⟨⟨j, hj⟩, rfl⟩
      have htr : ∀ (s : Bool) (h : ε j = s), (⟨j, h⟩ : {i : Fin n // ε i = s}) ∈ T s := by
        rintro s rfl
        exact hj
      have hback : ∀ (s : Bool) (i' : {i : Fin n // ε i = s}), i' ∈ T s →
          ∃ y, (∃ a ∈ T s, b s a = y) ∧ ext0 ε s y = M *ᵥ Pi.single i'.1 1 :=
        fun s i' hi' => ⟨b s i', ⟨i', hi', rfl⟩, (hMcol s i').symm⟩
      rcases Bool.eq_false_or_eq_true (ε j) with h | h
      · exact Or.inl (hback _ ⟨j, h⟩ (htr _ h))
      · exact Or.inr (hback _ ⟨j, h⟩ (htr _ h))
  conv_lhs => rw [hdecomp, hT true, hT false]
  rw [Submodule.map_span, Submodule.map_span, Submodule.map_span, ← Submodule.span_union, hset,
    Set.range_comp]
end GlobalTheory.CompanionTheory.JStable
