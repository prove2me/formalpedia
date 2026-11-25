-- Prove2me | solution 1 for GlobalTheory.WachFree.basis_of_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:38:27.099213+00:00
-- url     : https://prove2.me/submissions/ff9913bf-47c4-4a58-9b6b-cb90c20d90d2

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvrComplete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemXSmulOfProjective
import Theorems.Thm_GlobalTheory_WachFree_finrank_fibre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct
open GlobalTheory GlobalTheory.WachFree
namespace GlobalTheory.WachFree
theorem _root_.solution {ι R N E D : Type} [Finite ι] [CommRing R] [IsLocalRing R]
    [AddCommGroup N] [Module (ι → R) N] [Module.Finite (ι → R) N] [Module R N]
    [IsScalarTower R (ι → R) N] [Module.Flat R N] [CommRing E] [Algebra (ι → R) E]
    (hE : Function.Injective (algebraMap (ι → R) E)) [AddCommGroup D] [Module E D]
    [Module (ι → R) D] [IsScalarTower (ι → R) E D] [Module.Free E D] (f : N →ₗ[ι → R] D)
    (hf : IsBaseChange E f) : Nonempty (Module.Basis (Fin (Module.finrank E D)) (ι → R) N) := by
  classical
  haveI := Fintype.ofFinite ι
  haveI : Module.Flat (ι → R) N := Algebra.FormallyUnramified.flat_of_restrictScalars R (ι → R) N
  haveI : Finite (MaximalSpectrum (ι → R)) := by
    haveI := (Algebra.QuasiFinite.finite_primesOver (S := ι → R)
      (IsLocalRing.maximalIdeal R)).to_subtype
    refine Finite.of_injective (fun n : MaximalSpectrum (ι → R) =>
      (⟨n.asIdeal, n.isMaximal.isPrime, ⟨(IsLocalRing.eq_maximalIdeal
        (@Ideal.isMaximal_comap_of_isIntegral_of_isMaximal R _ _ _ _ _ n.asIdeal n.isMaximal)).symm⟩⟩ :
        (IsLocalRing.maximalIdeal R).primesOver (ι → R))) fun a b hab => ?_
    exact MaximalSpectrum.ext (congrArg Subtype.val hab)
  refine Module.nonempty_basis_of_flat_of_finrank_eq _ _ _ fun P => ?_
  haveI := P.isMaximal
  have hee : ∀ i : ι, (Pi.single i 1 : ι → R) * (Pi.single i 1 - 1) = 0 := by
    intro i
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  obtain ⟨i, hi⟩ : ∃ i : ι, (Pi.single i 1 : ι → R) ∉ P.asIdeal := by
    by_contra hcon
    push Not at hcon
    apply P.isMaximal.ne_top
    rw [Ideal.eq_top_iff_one, ← Finset.univ_sum_single (1 : ι → R)]
    exact Ideal.sum_mem _ fun j _ => hcon j
  have hi' : (Pi.single i 1 - 1 : ι → R) ∈ P.asIdeal :=
    (P.isMaximal.isPrime.mem_or_mem (by rw [hee i]; exact Ideal.zero_mem _)).resolve_left hi
  obtain ⟨r, hr⟩ := finrank_fibre (R := R) (N := N) i
  rw [hr ((ι → R) ⧸ P.asIdeal) (by
    rw [Ideal.Quotient.algebraMap_eq, ← map_one (Ideal.Quotient.mk P.asIdeal), Ideal.Quotient.eq]
    exact hi')]
  let I : Ideal E := Ideal.span {algebraMap (ι → R) E (Pi.single i 1 - 1)}
  haveI : Nontrivial (E ⧸ I) := by
    rw [Ideal.Quotient.nontrivial_iff]
    intro hI
    rw [Ideal.span_singleton_eq_top] at hI
    apply hi
    have : algebraMap (ι → R) E (Pi.single i 1) = 0 := by
      rw [← hI.mul_left_eq_zero, ← map_mul, hee, map_zero]
    rw [hE (this.trans (map_zero _).symm)]
    exact Ideal.zero_mem _
  haveI : Nontrivial E := (algebraMap E (E ⧸ I)).domain_nontrivial
  rw [← hr (E ⧸ I) (by
    rw [IsScalarTower.algebraMap_apply (ι → R) E (E ⧸ I), Ideal.Quotient.algebraMap_eq,
      ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]
    exact Ideal.subset_span (by simp)),
    ← (AlgebraTensorModule.cancelBaseChange (ι → R) E (E ⧸ I) (E ⧸ I) N).finrank_eq,
    (AlgebraTensorModule.congr (LinearEquiv.refl (E ⧸ I) (E ⧸ I)) hf.equiv).finrank_eq,
    Module.finrank_baseChange]
end GlobalTheory.WachFree
