-- Prove2me | solution 1 for GlobalTheory.UnitLemma.exists_aeval_eq_of_charpoly_separable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:38:27.523425+00:00
-- url     : https://prove2.me/submissions/f6362441-e9b3-444f-a102-ca1cedef2c17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CharpolyDvdPowFinrankOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAevalEqOfCharpolySeparableInvolution
import Theorems.Thm_GlobalTheory_CharpolyDvd_charpoly_dvd_pow_finrank


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma
namespace GlobalTheory.UnitLemma
theorem _root_.solution {E A : Type} [Field E] [CommRing A] [Algebra E A]
    [Module.Finite E A] (g : A) (hP : (LinearMap.mulLeft E g).charpoly.Separable) (a : A) :
    ∃ f : E[X], a = aeval g f := by
  classical
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact ⟨0, Subsingleton.elim _ _⟩
  have hint : IsIntegral E g := Algebra.IsIntegral.isIntegral g
  have hm0 : minpoly E g ≠ 0 := minpoly.ne_zero hint
  have hf : aeval (LinearMap.mulLeft E g) (minpoly E g) = 0 := by
    have := aeval_algHom_apply (Algebra.lmul E A) g (minpoly E g)
    rw [minpoly.aeval, map_zero] at this
    exact this
  have hn : 0 < Module.finrank E A := Module.finrank_pos
  have h1 := GlobalTheory.CharpolyDvd.charpoly_dvd_pow_finrank _ _ hf
  have h2 : (LinearMap.mulLeft E g).charpoly ∣ minpoly E g :=
    (hP.squarefree.dvd_pow_iff_dvd hn.ne').1 h1
  have h3 : Module.finrank E A ≤ (minpoly E g).natDegree := by
    have := natDegree_le_of_dvd h2 hm0
    rwa [LinearMap.charpoly_natDegree] at this
  have hli := linearIndependent_pow (K := E) g
  have h4 := hli.fintype_card_le_finrank
  rw [Fintype.card_fin] at h4
  haveI : Nonempty (Fin (minpoly E g).natDegree) := ⟨⟨0, by omega⟩⟩
  have htop := hli.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin]; omega)
  have hle : Submodule.span E (Set.range fun i : Fin (minpoly E g).natDegree => g ^ (i : ℕ)) ≤
      Subalgebra.toSubmodule (Algebra.adjoin E {g}) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hg : g ∈ Algebra.adjoin E {g} := Algebra.subset_adjoin (Set.mem_singleton g)
    exact Subalgebra.pow_mem (Algebra.adjoin E {g}) hg (i : ℕ)
  have ha : a ∈ Algebra.adjoin E {g} := by
    have : a ∈ Submodule.span E (Set.range fun i : Fin (minpoly E g).natDegree => g ^ (i : ℕ)) := by
      rw [htop]; trivial
    exact hle this
  rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
  obtain ⟨f, hf⟩ := ha
  exact ⟨f, hf.symm⟩
end GlobalTheory.UnitLemma
